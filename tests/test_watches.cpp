// WatchLists (one pool for all watch lists) against a vector-of-vectors model: random pushes,
// pops, truncations, reserves, shrinks and compactions (with the room they give lists of
// long-clause watches), in normal and in stress mode.

#include <cstdint>
#include <random>
#include <vector>

#include "psat/solver/watches.hpp"
#include "test_framework.hpp"

using psat::Watch;
using psat::WatchLists;

namespace {

bool same(const WatchLists& a, const std::vector<std::vector<Watch>>& model) {
  if (a.size() != model.size()) return false;
  for (size_t l = 0; l < model.size(); ++l) {
    const auto list = a[l];
    if (list.size() != model[l].size()) return false;
    for (size_t i = 0; i < list.size(); ++i) {
      if (list[i].blit != model[l][i].blit || list[i].ref != model[l][i].ref) return false;
    }
  }
  return true;
}

void run(bool stress, uint64_t seed) {
  std::mt19937_64 rng(seed);
  WatchLists lists;
  lists.set_stress(stress);
  std::vector<std::vector<Watch>> model;
  lists.resize(40);
  model.resize(40);
  for (int step = 0; step < 20000; ++step) {
    const size_t l = rng() % model.size();
    const int op = static_cast<int>(rng() % 100);
    if (op < 60) {
      const Watch w{static_cast<uint32_t>(rng() % 1000), static_cast<uint32_t>(rng())};
      lists[l].push_back(w);
      model[l].push_back(w);
    } else if (op < 70) {
      if (!model[l].empty()) {
        lists[l].pop_back();
        model[l].pop_back();
      }
    } else if (op < 78) {
      const size_t n = model[l].empty() ? 0 : rng() % (model[l].size() + 1);
      lists[l].resize(n);
      model[l].resize(n);
    } else if (op < 82) {
      lists[l].reserve(model[l].size() + rng() % 20);
    } else if (op < 86) {
      lists[l].shrink_to_fit();
    } else if (op < 88) {
      lists.compact();
    } else if (op < 91) {
      lists.maybe_compact();
    } else if (op < 92) {
      if (lists.compact_due()) lists.compact();  // (as at a restart)
    } else if (op < 93) {
      lists.resize(model.size() + 3);
      model.resize(model.size() + 3);
    } else {  // overwrite in place (as propagation does with blocking literals)
      if (!model[l].empty()) {
        const size_t i = rng() % model[l].size();
        lists[l][i].blit = model[l][i].blit = static_cast<uint32_t>(rng() % 1000);
      }
    }
    if (step % 97 == 0) CHECK(same(lists, model));
  }
  CHECK(same(lists, model));
  size_t live = 0;
  for (const auto& m : model) live += m.size();
  CHECK_EQ(lists.live(), live);
  lists.compact();
  CHECK(same(lists, model));
  CHECK_EQ(lists.garbage(), size_t{0});
  // Unused capacity after a compaction: the room for long-clause watches (a quarter + 2 per list).
  size_t room = 0;
  for (const auto& m : model) {
    size_t longs = 0;
    for (const Watch& w : m) longs += !w.binary();
    room += longs ? longs / 4 + 2 : 0;
  }
  CHECK_EQ(lists.slack(), room);
}

}  // namespace

TEST(watch_lists_model) {
  run(false, 1);
  run(false, 2);
  run(true, 3);
}

// Pushing to one list while iterating another by index into the pool (as propagation does):
// the begin index of the iterated list survives relocations of the other list.
TEST(watch_lists_begin_index_survives_relocation) {
  for (int stress = 0; stress < 2; ++stress) {
    WatchLists lists;
    lists.set_stress(stress != 0);
    lists.resize(4);
    for (uint32_t i = 0; i < 100; ++i) lists[0].push_back(Watch{i, i});
    const uint32_t begin = lists.begin_index(0);
    for (uint32_t i = 0; i < 1000; ++i) {
      lists[1 + i % 3].push_back(Watch{i, 0});
      CHECK_EQ(lists.begin_index(0), begin);
      CHECK_EQ(lists.pool()[begin + (i % 100)].blit, i % 100);
    }
  }
}
