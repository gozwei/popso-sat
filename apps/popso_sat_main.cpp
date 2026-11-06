// popso-sat command line: SAT Competition input/output conventions.
//
//   popso-sat [options] <input.cnf | .cnf.gz | .cnf.xz | -> [<proof-file>]
//
// Prints 'c' comments, then 's SATISFIABLE' with 'v ... 0' model lines, 's UNSATISFIABLE' or
// 's UNKNOWN'; exit code 10 / 20 / 0, and 1 on errors.

#include <atomic>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "psat/core/options.hpp"
#include "psat/io/dimacs.hpp"
#include "psat/io/input.hpp"
#include "psat/io/proof.hpp"
#include "psat/solver/solver.hpp"

namespace {

std::atomic<bool> g_interrupt{false};
std::atomic<int> g_signals{0};
bool g_quiet = false;

extern "C" void on_signal(int sig) {
  // A second Ctrl-C gives up immediately. A repeated SIGTERM does not: GNU timeout (and other
  // runners) send it to the process and to its process group, so it often arrives twice at once,
  // and the solver should still stop cleanly with its answer line and statistics.
  if (sig == SIGINT && g_signals.fetch_add(1) > 0) std::_Exit(128 + sig);
  g_interrupt.store(true);
}

void usage(std::FILE* out) {
  std::fprintf(out,
               "usage: popso-sat [options] <input.cnf | .cnf.gz | .cnf.xz | -> [<proof-file>]\n"
               "\n"
               "  -h, --help            this help\n"
               "  --version             print the version\n"
               "  -v, --verbose         more output (repeatable)\n"
               "  -q, --quiet           no 'c' output\n"
               "  -n, --no-model        do not print the model ('v' lines)\n"
               "  --proof=<file>        write a DRAT proof (binary; --proof-text for text format)\n"
               "  --proof-text          text DRAT proof\n"
               "  -t <s>, --time-limit=<s>  wall-clock limit in seconds\n"
               "  --mem-limit=<MB>      memory limit: s UNKNOWN once the peak resident size reaches 7/8 of it\n"
               "  --conflicts=<n>       conflict limit\n"
               "  --threads=<n>         accepted for compatibility; popso-sat is single-threaded for now\n"
               "  --relaxed             accept malformed-but-unambiguous DIMACS (same as --strict=0)\n"
               "\n"
               "solver options (--name=<value>, --name for 1, --no-name for 0):\n");
  psat::Options::print_help(out);
}

// The input formula for the final model check: flat clauses with 0 terminators in fixed-size
// chunks (a growing vector would briefly hold two copies when it reallocates: hundreds of MB on
// the largest competition formulas).
struct Original {
  static constexpr size_t kChunk = size_t{1} << 20;
  std::vector<std::vector<int>> chunks;
  void push(int x) {
    if (chunks.empty() || chunks.back().size() == kChunk) {
      chunks.emplace_back();
      chunks.back().reserve(kChunk);
    }
    chunks.back().push_back(x);
  }
};

struct Loader : psat::DimacsHandler {
  psat::Solver& solver;
  Original* original;  // or null
  explicit Loader(psat::Solver& s, Original* orig) : solver(s), original(orig) {}
  void header(int vars, int64_t clauses) override {
    solver.reserve(vars);
    solver.reserve_clauses(clauses);
  }
  void clause(const int* lits, size_t n) override {
    solver.add_clause(lits, n);
    if (original) {
      for (size_t i = 0; i < n; ++i) original->push(lits[i]);
      original->push(0);
    }
  }
};

// 'v' lines of at most 78 characters (plus the final " 0"), written through a fixed buffer: the
// model is printed after 's SATISFIABLE', so it must not allocate (running out of memory there
// would leave the answer without its model; a string of the whole model takes hundreds of MB on
// the largest formulas).
void print_model(const psat::Solver& solver, int max_var) {
  static char out[1 << 16];
  size_t pos = 0, line = 1;  // line: length of the current line
  out[pos++] = 'v';
  char buf[16];
  for (int v = 1; v <= max_var; ++v) {
    const int len = std::snprintf(buf, sizeof(buf), " %d", solver.val(v));
    if (pos + sizeof(buf) + 2 > sizeof(out)) {
      std::fwrite(out, 1, pos, stdout);
      pos = 0;
    }
    if (line + static_cast<size_t>(len) > 78) {
      out[pos++] = '\n';
      out[pos++] = 'v';
      line = 1;
    }
    std::memcpy(out + pos, buf, static_cast<size_t>(len));
    pos += static_cast<size_t>(len);
    line += static_cast<size_t>(len);
  }
  if (pos + 3 > sizeof(out)) {
    std::fwrite(out, 1, pos, stdout);
    pos = 0;
  }
  std::memcpy(out + pos, " 0\n", 3);
  std::fwrite(out, 1, pos + 3, stdout);
}

// Out of memory before an answer: 's UNKNOWN' (exit 0), not an error exit or an abort.
int out_of_memory(bool quiet) {
  if (!quiet) std::printf("c out of memory\n");
  std::printf("s UNKNOWN\n");
  std::fflush(stdout);
  return 0;
}

// Index of the first clause the model falsifies, or -1.
long long check_model(const psat::Solver& solver, const Original& original) {
  long long idx = 0;
  bool sat = false;
  for (const auto& chunk : original.chunks) {
    for (const int lit : chunk) {
      if (lit == 0) {
        if (!sat) return idx;
        ++idx;
        sat = false;
      } else if (!sat && solver.val(lit) == lit) {
        sat = true;
      }
    }
  }
  return -1;
}

int run(int argc, char** argv) {
  psat::Options opts;
  std::string input, proof_path;
  bool quiet = false, print_model_lines = true, proof_text = false;
  double time_limit = 0;
  long long mem_limit_mb = 0, conflict_limit = -1;
  int verbose = 0;
  std::vector<std::string> positional;

  try {
    for (int i = 1; i < argc; ++i) {
      std::string a = argv[i];
      auto next_value = [&](const char* name) -> std::string {
        if (i + 1 >= argc) throw std::invalid_argument(std::string("missing value for ") + name);
        return argv[++i];
      };
      if (a == "-h" || a == "--help") {
        usage(stdout);
        return 0;
      } else if (a == "--version") {
        std::printf("%s\n", PSAT_VERSION);
        return 0;
      } else if (a == "-v" || a == "--verbose") {
        ++verbose;
      } else if (a == "-q" || a == "--quiet") {
        quiet = true;
      } else if (a == "-n" || a == "--no-model") {
        print_model_lines = false;
      } else if (a == "--proof-text") {
        proof_text = true;
      } else if (a == "--relaxed") {
        opts.strict = 0;
      } else if (a == "-t") {
        time_limit = std::stod(next_value("-t"));
      } else if (a == "-" || a[0] != '-') {
        positional.push_back(a);
      } else if (a.rfind("--", 0) == 0) {
        std::string name = a.substr(2), value = "1";
        const size_t eq = name.find('=');
        if (eq != std::string::npos) {
          value = name.substr(eq + 1);
          name = name.substr(0, eq);
        } else if (name.rfind("no-", 0) == 0 && opts.has(name.substr(3))) {
          name = name.substr(3);
          value = "0";
        }
        if (name == "proof") {
          proof_path = value;
        } else if (name == "time-limit" || name == "time") {
          time_limit = std::stod(value);
        } else if (name == "mem-limit") {
          mem_limit_mb = std::stoll(value);
        } else if (name == "conflicts") {
          conflict_limit = std::stoll(value);
        } else if (name == "threads") {
          (void)std::stoi(value);
        } else if (name == "verbose" && eq != std::string::npos) {
          verbose = std::stoi(value);
        } else if (!opts.set(name, value)) {
          throw std::invalid_argument("unknown option '" + a + "' (see --help)");
        }
      } else {
        throw std::invalid_argument("unknown option '" + a + "' (see --help)");
      }
    }
    if (positional.empty()) throw std::invalid_argument("no input file (see --help)");
    if (positional.size() > 2) throw std::invalid_argument("too many arguments (see --help)");
    input = positional[0];
    if (positional.size() == 2) {
      if (!proof_path.empty()) throw std::invalid_argument("proof file given twice");
      proof_path = positional[1];
    }
  } catch (const std::bad_alloc&) {
    throw;
  } catch (const std::exception& e) {
    std::fprintf(stderr, "c ERROR: %s\n", e.what());
    return 1;
  }
  if (verbose > opts.verbose) opts.verbose = verbose;
  if (proof_text) opts.binaryproof = 0;
  g_quiet = quiet;

  std::signal(SIGINT, on_signal);
  std::signal(SIGTERM, on_signal);
#ifdef SIGXCPU
  std::signal(SIGXCPU, on_signal);
#endif

  if (!quiet) {
    std::printf("c popso-sat %s (Polkowski's Optimization Solver, SAT)\n", PSAT_VERSION);
    opts.print_changed(stdout);
  }

  psat::Solver solver(opts);
  solver.set_terminate(&g_interrupt);
  if (time_limit > 0) solver.set_time_limit(time_limit);
  if (conflict_limit >= 0) solver.set_conflict_limit(conflict_limit);
  if (mem_limit_mb > 0) solver.set_memory_limit(static_cast<uint64_t>(mem_limit_mb) << 20);

  std::unique_ptr<std::FILE, int (*)(std::FILE*)> proof_file(nullptr, &std::fclose);
  std::unique_ptr<psat::ProofWriter> proof;
  if (!proof_path.empty()) {
    std::FILE* f = std::fopen(proof_path.c_str(), "wb");
    if (!f) {
      std::fprintf(stderr, "c ERROR: cannot open proof file '%s'\n", proof_path.c_str());
      return 1;
    }
    proof_file.reset(f);
    proof = std::make_unique<psat::ProofWriter>(f, opts.binaryproof != 0);
    solver.set_proof(proof.get());
  }

  Original original;
  int max_var = 0;
  try {
    Loader loader(solver, opts.check ? &original : nullptr);
    psat::DimacsParser parser(loader, opts.strict != 0);
    psat::stream_input(input, [&](const char* d, size_t n) { parser.feed(d, n); });
    parser.finish();
    max_var = std::max(parser.has_header() ? parser.header_vars() : 0, parser.max_var());
    solver.reserve(max_var);
    if (!quiet) {
      std::printf("c parsed %d variables, %lld clauses in %.2f s\n", max_var,
                  static_cast<long long>(parser.clauses()), solver.seconds());
      std::fflush(stdout);
    }
  } catch (const std::bad_alloc&) {
    return out_of_memory(quiet);
  } catch (const std::exception& e) {
    std::fprintf(stderr, "c ERROR: %s\n", e.what());
    return 1;
  }

  int res = psat::kUnknown;
  try {
    res = solver.solve();
  } catch (const std::bad_alloc&) {
    if (!quiet) std::printf("c out of memory\n");
    res = psat::kUnknown;
  } catch (const std::exception& e) {
    std::fprintf(stderr, "c ERROR: %s\n", e.what());
    if (!quiet) std::printf("c ERROR: %s\n", e.what());
    res = psat::kUnknown;
  }
  // The proof is complete on disk (flushed, closed, no write error) before an answer is printed:
  // 's UNSATISFIABLE' with a truncated proof would be rejected by the checker.
  if (proof) {
    proof->flush();
    std::FILE* f = proof_file.release();
    const bool write_error = proof->failed() || std::fflush(f) != 0 || std::ferror(f) != 0;
    const bool close_error = std::fclose(f) != 0;
    if (write_error || close_error) {
      std::fprintf(stderr, "c ERROR: writing the proof file '%s' failed\n", proof_path.c_str());
      if (!quiet) std::printf("c ERROR: writing the proof file failed\n");
      if (res == psat::kUnsat) res = psat::kUnknown;
    }
  }

  if (res == psat::kSat && opts.check) {
    const long long bad = check_model(solver, original);
    if (bad >= 0) {
      std::fprintf(stderr, "c ERROR: internal model check failed on clause %lld (solver bug)\n", bad);
      std::printf("c ERROR: internal model check failed\ns UNKNOWN\n");
      return 1;
    }
  }
  if (!quiet) {
    if (opts.verbose) solver.print_statistics(stdout);
    if (res == psat::kUnknown && *solver.unknown_reason()) std::printf("c stopped: %s\n", solver.unknown_reason());
    std::printf("c solved in %.2f s\n", solver.seconds());
  }
  if (res == psat::kSat) {
    std::printf("s SATISFIABLE\n");
    if (print_model_lines) print_model(solver, max_var);
  } else if (res == psat::kUnsat) {
    std::printf("s UNSATISFIABLE\n");
  } else {
    std::printf("s UNKNOWN\n");
  }
  std::fflush(stdout);
  return res;
}

}  // namespace

int main(int argc, char** argv) {
  // The C++ runtime allocates a thread's exception state when the thread throws for the first
  // time; if that is the std::bad_alloc of an exhausted heap, the throw itself crashes (SIGSEGV in
  // __cxa_throw with macOS libc++abi). One exception at startup sets it up while memory is free.
  try {
    throw std::bad_alloc();
  } catch (const std::bad_alloc&) {
  }
  // Running out of memory before the answer (setup, parsing, search) gives 's UNKNOWN'; nothing
  // after the 's' line allocates.
  try {
    return run(argc, argv);
  } catch (const std::bad_alloc&) {
    return out_of_memory(g_quiet);
  } catch (const std::exception& e) {
    std::fprintf(stderr, "c ERROR: %s\n", e.what());
    return 1;
  }
}
