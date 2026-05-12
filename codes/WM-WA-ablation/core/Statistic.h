#ifndef WMAXCDCL_STATISTIC_H
#define WMAXCDCL_STATISTIC_H

#include <algorithm>
#include <cassert>
#include <cmath>
#include <limits>
#include <vector>

namespace Minisat {

constexpr double STATISTIC_MAX_VALUE = 1LL << 50;
constexpr double STATISTIC_MIN_VALUE = -STATISTIC_MAX_VALUE;

/* Statistc values with a window size limit.
 * Old data will be overwrite if statistic data number exceed window size.
 */
template <typename T>
class StatisticWindow {
 public:
  StatisticWindow(size_t window_size) : data_(window_size, 0) {}
  ~StatisticWindow() {}

  /* Add a new statistic value. */
  void put(const T& value) {
    assert(value < STATISTIC_MAX_VALUE);
    assert(value > STATISTIC_MIN_VALUE);
    if (index_ >= data_.size()) {
      index_ = 0;
    }
    sum_ -= static_cast<double>(data_[index_]);
    data_[index_] = value;
    sum_ += static_cast<double>(value);
    index_++;
    put_count_++;
  }

  size_t window_size() const { return data_.size(); }

  /* Adjust the statistic window size, historical statistic data will be cleared
   * after resize. */
  void resize_window(size_t window_size) {
    clear();
    data_.resize(window_size);
    index_ = 0;
  }

  bool empty() const { return data_.empty(); }

  void clear() {
    data_.clear();
    sum_ = 0.0;
  }

  /* Return the maximum value in statistic window.
   * Time complexity: O(n)
   */
  T max() const {
    T max_val = std::numeric_limits<T>::min();
    for (T& val : data_) {
      if (max_val < val) {
        max_val = val;
      }
    }
    return max_val;
  }

  /* Return the minimum value in statistic window.
   * Time complexity: O(n)
   */
  T min() const {
    T min_val = std::numeric_limits<T>::max();
    for (T& val : data_) {
      if (min_val > val) {
        min_val = val;
      }
    }
    return min_val;
  }

  /* Return the summary value in statistic window.
   * Time complexity: O(1)
   */
  double sum() const { return sum_; }

  /* Return the avarage value in statistic window.
   * Time complexity: O(1)
   */
  double mean() const {
    if (data_.empty()) return 0;
    if (put_count_ == index_) {
      return sum_ / static_cast<double>(index_);
    } else {
      return sum_ / static_cast<double>(data_.size());
    }
  }

  /* Return the median value in statistic window.
   * Time complexity: O(n)
   */
  T median() const {
    if (data_.empty()) return 0;
    std::vector<T> copy = data_;
    std::sort(copy.begin(), copy.end());
    if (copy.size() % 2 == 0) {
      return (copy[copy.size() / 2 - 1] + copy[copy.size() / 2]) / 2;
    } else {
      return copy[copy.size() / 2];
    }
  }

  /* Return the standard deviation value in statistic window.
   * Time complexity: O(n)
   */
  double standard_deviation() const {
    if (data_.empty()) return 0;
    double mean_value = mean();
    double sum = 0.0;
    for (const auto& value : data_) {
      sum += (value - mean_value) * (value - mean_value);
    }
    return std::sqrt(sum / data_.size());
  }

 private:
  size_t put_count_ = 0;
  size_t index_ = 0;
  double sum_ = 0.0;
  std::vector<T> data_;
};

class StatisticAverage {
 public:
  StatisticAverage() {}
  ~StatisticAverage() {}

  void put(double value) {
    sum_ += value;
    count_ += 1;
  }

  double mean() {
    if (count_ == 0) return 0.0;
    return sum_ / count_;
  }

  double sum() { return sum_; }

  double count() { return count_; }

  void reset() {
    sum_ = 0.0;
    count_ = 0;
  }

 private:
  double sum_ = 0.0;
  size_t count_ = 0;
};

}  // namespace Minisat

#endif  // WMAXCDCL_STATISTIC_H
