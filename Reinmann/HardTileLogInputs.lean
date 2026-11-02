/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.CertifiedComplexInputs
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Explicit logarithms for the degree-eight hard-tile finite model.
Every decimal centre is a rational, checked against a Mathlib series bound. -/
noncomputable section
namespace Reinmann.HardTileLogInputs
open CertifiedComplexInputs
set_option maxRecDepth 10000

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_2 : |Real.log (2:ℝ) - ((138629436111989 / 200000000000000):ℝ)| ≤ (1 / 10 ^ 15:ℝ) := by
  convert log_enclosure (q := 2) (a := (138629436111989 / 200000000000000)) (e := 1 / 10 ^ 15) (by norm_num) 20
    (by norm_num [logError, logPartial, Finset.sum_range_succ]) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_3 : |Real.log (3:ℝ) - ((109861228866811 / 100000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (3 / 2)) (a := (138629436111989 / 200000000000000)) (b := (101366277027041 / 250000000000000)) 1
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (1 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(1 * (138629436111989 / 200000000000000) + (101366277027041 / 250000000000000):ℚ) - (109861228866811 / 100000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_4 : |Real.log (4:ℝ) - ((138629436111989 / 100000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := 1) (a := (138629436111989 / 200000000000000)) (b := 0) 2
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (2 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(2 * (138629436111989 / 200000000000000) + 0:ℚ) - (138629436111989 / 100000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_5 : |Real.log (5:ℝ) - ((16094379124341 / 10000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (5 / 4)) (a := (138629436111989 / 200000000000000)) (b := (22314355131421 / 100000000000000)) 2
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (2 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(2 * (138629436111989 / 200000000000000) + (22314355131421 / 100000000000000):ℚ) - (16094379124341 / 10000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_6 : |Real.log (6:ℝ) - ((358351893845611 / 200000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (3 / 2)) (a := (138629436111989 / 200000000000000)) (b := (101366277027041 / 250000000000000)) 2
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (2 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(2 * (138629436111989 / 200000000000000) + (101366277027041 / 250000000000000):ℚ) - (358351893845611 / 200000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_7 : |Real.log (7:ℝ) - ((1945910149055313 / 1000000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (7 / 4)) (a := (138629436111989 / 200000000000000)) (b := (559615787935423 / 1000000000000000)) 2
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (2 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(2 * (138629436111989 / 200000000000000) + (559615787935423 / 1000000000000000):ℚ) - (1945910149055313 / 1000000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_8 : |Real.log (8:ℝ) - ((519860385419959 / 250000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := 1) (a := (138629436111989 / 200000000000000)) (b := 0) 3
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (3 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(3 * (138629436111989 / 200000000000000) + 0:ℚ) - (519860385419959 / 250000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_9 : |Real.log (9:ℝ) - ((109861228866811 / 50000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (9 / 8)) (a := (138629436111989 / 200000000000000)) (b := (117783035656383 / 1000000000000000)) 3
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (3 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(3 * (138629436111989 / 200000000000000) + (117783035656383 / 1000000000000000):ℚ) - (109861228866811 / 50000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_10 : |Real.log (10:ℝ) - ((1151292546497023 / 500000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (5 / 4)) (a := (138629436111989 / 200000000000000)) (b := (22314355131421 / 100000000000000)) 3
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (3 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(3 * (138629436111989 / 200000000000000) + (22314355131421 / 100000000000000):ℚ) - (1151292546497023 / 500000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_11 : |Real.log (11:ℝ) - ((239789527279837 / 100000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (11 / 8)) (a := (138629436111989 / 200000000000000)) (b := (63690746223707 / 200000000000000)) 3
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (3 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(3 * (138629436111989 / 200000000000000) + (63690746223707 / 200000000000000):ℚ) - (239789527279837 / 100000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_12 : |Real.log (12:ℝ) - ((621226662447 / 250000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (3 / 2)) (a := (138629436111989 / 200000000000000)) (b := (101366277027041 / 250000000000000)) 3
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (3 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(3 * (138629436111989 / 200000000000000) + (101366277027041 / 250000000000000):ℚ) - (621226662447 / 250000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_13 : |Real.log (13:ℝ) - ((80154667420673 / 31250000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (13 / 8)) (a := (138629436111989 / 200000000000000)) (b := (485507815781701 / 1000000000000000)) 3
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (3 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(3 * (138629436111989 / 200000000000000) + (485507815781701 / 1000000000000000):ℚ) - (80154667420673 / 31250000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_14 : |Real.log (14:ℝ) - ((1319528664807629 / 500000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (7 / 4)) (a := (138629436111989 / 200000000000000)) (b := (559615787935423 / 1000000000000000)) 3
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (3 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(3 * (138629436111989 / 200000000000000) + (559615787935423 / 1000000000000000):ℚ) - (1319528664807629 / 500000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_15 : |Real.log (15:ℝ) - ((270805020110221 / 100000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (15 / 8)) (a := (138629436111989 / 200000000000000)) (b := (314304329711187 / 500000000000000)) 3
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (3 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(3 * (138629436111989 / 200000000000000) + (314304329711187 / 500000000000000):ℚ) - (270805020110221 / 100000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_16 : |Real.log (16:ℝ) - ((2772588722239781 / 1000000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := 1) (a := (138629436111989 / 200000000000000)) (b := 0) 4
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(4 * (138629436111989 / 200000000000000) + 0:ℚ) - (2772588722239781 / 1000000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_17 : |Real.log (17:ℝ) - ((354151668007027 / 125000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (17 / 16)) (a := (138629436111989 / 200000000000000)) (b := (12124924363287 / 200000000000000)) 4
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(4 * (138629436111989 / 200000000000000) + (12124924363287 / 200000000000000):ℚ) - (354151668007027 / 125000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_18 : |Real.log (18:ℝ) - ((722592939474041 / 250000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (9 / 8)) (a := (138629436111989 / 200000000000000)) (b := (117783035656383 / 1000000000000000)) 4
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(4 * (138629436111989 / 200000000000000) + (117783035656383 / 1000000000000000):ℚ) - (722592939474041 / 250000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_19 : |Real.log (19:ℝ) - ((73610974479161 / 25000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (19 / 16)) (a := (138629436111989 / 200000000000000)) (b := (171850256926659 / 1000000000000000)) 4
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(4 * (138629436111989 / 200000000000000) + (171850256926659 / 1000000000000000):ℚ) - (73610974479161 / 25000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_20 : |Real.log (20:ℝ) - ((2995732273553991 / 1000000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (5 / 4)) (a := (138629436111989 / 200000000000000)) (b := (22314355131421 / 100000000000000)) 4
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(4 * (138629436111989 / 200000000000000) + (22314355131421 / 100000000000000):ℚ) - (2995732273553991 / 1000000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_21 : |Real.log (21:ℝ) - ((3044522437723423 / 1000000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (21 / 16)) (a := (138629436111989 / 200000000000000)) (b := (135966857741821 / 500000000000000)) 4
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(4 * (138629436111989 / 200000000000000) + (135966857741821 / 500000000000000):ℚ) - (3044522437723423 / 1000000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
private theorem log_pi_lo :
    |Real.log ((157079632679489661923 / 50000000000000000000):ℝ) - ((5723649429247 / 5000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (157079632679489661923 / 100000000000000000000)) (a := (138629436111989 / 200000000000000)) (b := (90316541057891 / 200000000000000)) 1
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (1 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(1 * (138629436111989 / 200000000000000) + (90316541057891 / 200000000000000):ℚ) - (5723649429247 / 5000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
private theorem log_pi_hi :
    |Real.log ((314159265358979323847 / 100000000000000000000):ℝ) - ((5723649429247 / 5000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have h := log_scaled_enclosure (q := (314159265358979323847 / 200000000000000000000)) (a := (138629436111989 / 200000000000000)) (b := (90316541057891 / 200000000000000)) 1
    (by norm_num) (by convert log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (1 * (1 / 10 ^ 15) + 1 / 10 ^ 15:ℚ)+
    |(1 * (138629436111989 / 200000000000000) + (90316541057891 / 200000000000000):ℚ) - (5723649429247 / 5000000000000)| ≤ (6 / 10 ^ 15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
-- Bounded rational series / table arithmetic needs extra elaboration steps.
theorem log_pi : |Real.log Real.pi - ((5723649429247 / 5000000000000):ℝ)| ≤ (6 / 10 ^ 15:ℝ) := by
  have hlo := abs_le.mp log_pi_lo
  have hhi := abs_le.mp log_pi_hi
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<3.14159265358979323846)
    Real.pi_gt_d20.le
  have hh := Real.log_le_log Real.pi_pos Real.pi_lt_d20.le
  rw [abs_le]
  constructor <;> linarith

end Reinmann.HardTileLogInputs
