#pragma once
// Test-only forward DRAT proof checker and brute-force SAT oracle for small formulas.
//
// The checker keeps the clause database (original clauses plus proof additions minus deletions)
// and checks every added clause by unit propagation from its negation (RUP); failing that, by RAT
// on its first literal p: for every clause D with -p, C v (D - {-p}) must be RUP. A line whose
// first literal p occurs again is a PR line (DPR, as dpr-trim reads it): the clause C is the part
// before the last repetition of p, the witness w the rest (starting with p); then every clause D
// that w touches without satisfying it must have C v D|w RUP (D|w: D without the literals w
// falsifies). Propagation uses occurrence lists with false-literal counters, rebuilt per check:
// fine for the small formulas used in unit tests.

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace psat_test {

using ClauseList = std::vector<std::vector<int>>;

struct RupResult {
  bool ok = false;
  bool has_empty = false;
  size_t lemmas = 0, deletions = 0, pr = 0;
  std::string error;
};

class RupChecker {
 public:
  explicit RupChecker(int max_var) : max_var_(max_var) {}

  void add_original(const std::vector<int>& c) { insert(c); }

  // Parses a text DRAT proof and checks it. Stops at the first failing lemma.
  RupResult check_text_proof(const std::string& proof) {
    RupResult res;
    std::istringstream in(proof);
    std::string line;
    while (std::getline(in, line)) {
      if (line.empty()) continue;
      bool del = false;
      std::istringstream ls(line);
      std::string tok;
      std::vector<int> lits;
      bool terminated = false;
      while (ls >> tok) {
        if (tok == "d") {
          del = true;
          continue;
        }
        const int x = std::atoi(tok.c_str());
        if (x == 0) {
          terminated = true;
          break;
        }
        if (std::abs(x) > max_var_) max_var_ = std::abs(x);
        lits.push_back(x);
      }
      if (!terminated) {
        res.error = "unterminated proof line '" + line + "'";
        return res;
      }
      if (del) {
        ++res.deletions;
        if (!erase(lits)) {
          res.error = "deleting a clause not in the database: '" + line + "'";
          return res;
        }
        continue;
      }
      ++res.lemmas;
      std::vector<int> witness;
      for (size_t i = lits.size(); i-- > 1;) {
        if (lits[i] == lits[0]) {
          witness.assign(lits.begin() + static_cast<std::ptrdiff_t>(i), lits.end());
          lits.resize(i);
          break;
        }
      }
      if (!witness.empty()) ++res.pr;
      if (!rup(lits) && !(witness.empty() ? rat(lits) : pr(lits, witness))) {
        res.error = std::string("lemma is neither RUP nor ") + (witness.empty() ? "RAT" : "PR") + ": '" + line + "'";
        return res;
      }
      insert(lits);
      if (lits.empty()) {
        res.has_empty = true;
        break;
      }
    }
    res.ok = true;
    return res;
  }

 private:
  static std::vector<int> normalize(std::vector<int> c) {
    std::sort(c.begin(), c.end());
    c.erase(std::unique(c.begin(), c.end()), c.end());
    return c;
  }
  void insert(const std::vector<int>& c) { ++db_[normalize(c)]; }
  bool erase(const std::vector<int>& c) {
    auto it = db_.find(normalize(c));
    if (it == db_.end()) return false;
    if (--it->second == 0) db_.erase(it);
    return true;
  }

  // RAT on the first literal (the DRAT convention).
  bool rat(const std::vector<int>& c) {
    if (c.empty()) return false;
    const int p = c[0];
    std::vector<std::vector<int>> candidates;
    for (const auto& kv : db_) {
      if (std::find(kv.first.begin(), kv.first.end(), -p) != kv.first.end()) candidates.push_back(kv.first);
    }
    for (const auto& d : candidates) {
      std::vector<int> r = c;
      for (int l : d) {
        if (l != -p) r.push_back(l);
      }
      if (!rup(r)) return false;
    }
    return true;
  }

  // PR with witness w: w consistent and satisfying c; for every clause D touched but not satisfied
  // by w, c v D|w is RUP.
  bool pr(const std::vector<int>& c, const std::vector<int>& w) {
    std::set<int> ws(w.begin(), w.end());
    for (int l : w) {
      if (ws.count(-l)) return false;
    }
    bool satisfies = false;
    for (int l : c) satisfies = satisfies || ws.count(l) != 0;
    if (!satisfies) return false;
    std::vector<std::vector<int>> todo;
    for (const auto& kv : db_) {
      bool sat = false, touched = false;
      for (int l : kv.first) {
        sat = sat || ws.count(l) != 0;
        touched = touched || ws.count(-l) != 0;
      }
      if (sat || !touched) continue;
      std::vector<int> r = c;
      for (int l : kv.first) {
        if (!ws.count(-l)) r.push_back(l);
      }
      todo.push_back(std::move(r));
    }
    for (const auto& r : todo) {
      if (!rup(r)) return false;
    }
    return true;
  }

  // Unit propagation from the negation of c over the database; true if it reaches a conflict.
  bool rup(const std::vector<int>& c) {
    std::vector<int8_t> val(2 * static_cast<size_t>(max_var_) + 2, 0);
    auto idx = [](int lit) { return 2 * static_cast<size_t>(std::abs(lit)) + (lit < 0 ? 1 : 0); };
    std::vector<const std::vector<int>*> clauses;
    for (const auto& kv : db_) clauses.push_back(&kv.first);
    std::vector<std::vector<uint32_t>> occ(val.size());
    for (uint32_t i = 0; i < clauses.size(); ++i) {
      for (int l : *clauses[i]) occ[idx(l)].push_back(i);
    }
    std::vector<uint32_t> falses(clauses.size(), 0);
    std::vector<int> trail;
    auto assign = [&](int lit) -> bool {  // returns false on conflict with the current value
      if (val[idx(lit)] > 0) return true;
      if (val[idx(lit)] < 0) return false;
      val[idx(lit)] = 1;
      val[idx(-lit)] = -1;
      trail.push_back(lit);
      return true;
    };
    for (int l : c) {
      if (!assign(-l)) return true;  // c is a tautology
    }
    // Units and empty clauses in the database.
    for (const auto* cl : clauses) {
      if (cl->empty()) return true;
      if (cl->size() == 1 && !assign((*cl)[0])) return true;
    }
    for (size_t head = 0; head < trail.size(); ++head) {
      const int falsified = -trail[head];
      for (uint32_t ci : occ[idx(falsified)]) {
        const auto& cl = *clauses[ci];
        const uint32_t f = ++falses[ci];
        if (f + 1 < cl.size()) continue;
        int unassigned = 0, count = 0;
        bool sat = false;
        for (int l : cl) {
          const int8_t v = val[idx(l)];
          if (v > 0) {
            sat = true;
            break;
          }
          if (v == 0) {
            unassigned = l;
            ++count;
          }
        }
        if (sat) continue;
        if (count == 0) return true;
        if (count == 1 && !assign(unassigned)) return true;
      }
    }
    return false;
  }

  int max_var_;
  std::map<std::vector<int>, int> db_;
};

// Brute force: true if satisfiable (n <= ~20).
inline bool brute_force_sat(int n, const ClauseList& clauses) {
  for (uint64_t m = 0; m < (uint64_t{1} << n); ++m) {
    bool all = true;
    for (const auto& c : clauses) {
      bool sat = false;
      for (int l : c) {
        const bool bit = (m >> (std::abs(l) - 1)) & 1;
        if ((l > 0) == bit) {
          sat = true;
          break;
        }
      }
      if (!sat) {
        all = false;
        break;
      }
    }
    if (all) return true;
  }
  return false;
}

}  // namespace psat_test
