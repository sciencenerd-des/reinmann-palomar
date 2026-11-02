/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.HardTileLogInputs
public import Reinmann.CertifiedScalarExp

@[expose] public section

noncomputable section
namespace Reinmann.RectangleLogInputs
open CertifiedComplexInputs CertifiedTaylorModel
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000 in
theorem log_22 : |Real.log (22:ℝ)-((772760613339579/250000000000000):ℝ)| ≤ (8/10^15:ℝ) := by
  have h := log_scaled_enclosure (q := (11/8)) (a := (138629436111989/200000000000000)) (b := (63690746223707/200000000000000)) 4
    (by norm_num) (by convert HardTileLogInputs.log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4*(1/10^15)+1/10^15:ℚ)+
    |(4*(138629436111989/200000000000000)+(63690746223707/200000000000000):ℚ)-(772760613339579/250000000000000)| ≤ (8/10^15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
theorem log_23 : |Real.log (23:ℝ)-((62709884318583/20000000000000):ℝ)| ≤ (8/10^15:ℝ) := by
  have h := log_scaled_enclosure (q := (23/16)) (a := (138629436111989/200000000000000)) (b := (45363186711171/125000000000000)) 4
    (by norm_num) (by convert HardTileLogInputs.log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4*(1/10^15)+1/10^15:ℚ)+
    |(4*(138629436111989/200000000000000)+(45363186711171/125000000000000):ℚ)-(62709884318583/20000000000000)| ≤ (8/10^15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
theorem log_24 : |Real.log (24:ℝ)-((1589026915173973/500000000000000):ℝ)| ≤ (8/10^15:ℝ) := by
  have h := log_scaled_enclosure (q := (3/2)) (a := (138629436111989/200000000000000)) (b := (101366277027041/250000000000000)) 4
    (by norm_num) (by convert HardTileLogInputs.log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4*(1/10^15)+1/10^15:ℚ)+
    |(4*(138629436111989/200000000000000)+(101366277027041/250000000000000):ℚ)-(1589026915173973/500000000000000)| ≤ (8/10^15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
theorem log_25 : |Real.log (25:ℝ)-((16094379124341/5000000000000):ℝ)| ≤ (8/10^15:ℝ) := by
  have h := log_scaled_enclosure (q := (25/16)) (a := (138629436111989/200000000000000)) (b := (22314355131421/50000000000000)) 4
    (by norm_num) (by convert HardTileLogInputs.log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4*(1/10^15)+1/10^15:ℚ)+
    |(4*(138629436111989/200000000000000)+(22314355131421/50000000000000):ℚ)-(16094379124341/5000000000000)| ≤ (8/10^15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
theorem log_26 : |Real.log (26:ℝ)-((1629048269010741/500000000000000):ℝ)| ≤ (8/10^15:ℝ) := by
  have h := log_scaled_enclosure (q := (13/8)) (a := (138629436111989/200000000000000)) (b := (485507815781701/1000000000000000)) 4
    (by norm_num) (by convert HardTileLogInputs.log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4*(1/10^15)+1/10^15:ℚ)+
    |(4*(138629436111989/200000000000000)+(485507815781701/1000000000000000):ℚ)-(1629048269010741/500000000000000)| ≤ (8/10^15:ℚ) by norm_num) using 1 <;> norm_num

set_option maxHeartbeats 2000000 in
theorem log_27 : |Real.log (27:ℝ)-((3295836866004329/1000000000000000):ℝ)| ≤ (8/10^15:ℝ) := by
  have h := log_scaled_enclosure (q := (27/16)) (a := (138629436111989/200000000000000)) (b := (130812035941137/250000000000000)) 4
    (by norm_num) (by convert HardTileLogInputs.log_2 using 1 <;> norm_num)
    (by norm_num [logError, logPartial, Finset.sum_range_succ])
  convert log_recenter h (show (4*(1/10^15)+1/10^15:ℚ)+
    |(4*(138629436111989/200000000000000)+(130812035941137/250000000000000):ℚ)-(3295836866004329/1000000000000000)| ≤ (8/10^15:ℚ) by norm_num) using 1 <;> norm_num

def log2Disk : Disk := ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
theorem log2_contains : Contains log2Disk (Real.log (2:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_2 using 1 <;> norm_num [log2Disk]

def log3Disk : Disk := ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log3_contains : Contains log3Disk (Real.log (3:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_3 using 1 <;> norm_num [log3Disk]

def log4Disk : Disk := ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log4_contains : Contains log4Disk (Real.log (4:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_4 using 1 <;> norm_num [log4Disk]

def log5Disk : Disk := ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log5_contains : Contains log5Disk (Real.log (5:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_5 using 1 <;> norm_num [log5Disk]

def log6Disk : Disk := ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log6_contains : Contains log6Disk (Real.log (6:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_6 using 1 <;> norm_num [log6Disk]

def log7Disk : Disk := ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log7_contains : Contains log7Disk (Real.log (7:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_7 using 1 <;> norm_num [log7Disk]

def log8Disk : Disk := ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log8_contains : Contains log8Disk (Real.log (8:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_8 using 1 <;> norm_num [log8Disk]

def log9Disk : Disk := ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log9_contains : Contains log9Disk (Real.log (9:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_9 using 1 <;> norm_num [log9Disk]

def log10Disk : Disk := ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log10_contains : Contains log10Disk (Real.log (10:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_10 using 1 <;> norm_num [log10Disk]

def log11Disk : Disk := ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log11_contains : Contains log11Disk (Real.log (11:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_11 using 1 <;> norm_num [log11Disk]

def log12Disk : Disk := ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
theorem log12_contains : Contains log12Disk (Real.log (12:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_12 using 1 <;> norm_num [log12Disk]

def log13Disk : Disk := ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
theorem log13_contains : Contains log13Disk (Real.log (13:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_13 using 1 <;> norm_num [log13Disk]

def log14Disk : Disk := ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log14_contains : Contains log14Disk (Real.log (14:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_14 using 1 <;> norm_num [log14Disk]

def log15Disk : Disk := ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log15_contains : Contains log15Disk (Real.log (15:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_15 using 1 <;> norm_num [log15Disk]

def log16Disk : Disk := ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log16_contains : Contains log16Disk (Real.log (16:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_16 using 1 <;> norm_num [log16Disk]

def log17Disk : Disk := ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log17_contains : Contains log17Disk (Real.log (17:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_17 using 1 <;> norm_num [log17Disk]

def log18Disk : Disk := ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log18_contains : Contains log18Disk (Real.log (18:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_18 using 1 <;> norm_num [log18Disk]

def log19Disk : Disk := ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log19_contains : Contains log19Disk (Real.log (19:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_19 using 1 <;> norm_num [log19Disk]

def log20Disk : Disk := ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log20_contains : Contains log20Disk (Real.log (20:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_20 using 1 <;> norm_num [log20Disk]

def log21Disk : Disk := ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
theorem log21_contains : Contains log21Disk (Real.log (21:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_21 using 1 <;> norm_num [log21Disk]

def log22Disk : Disk := ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
theorem log22_contains : Contains log22Disk (Real.log (22:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert log_22 using 1 <;> norm_num [log22Disk]

def log23Disk : Disk := ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
theorem log23_contains : Contains log23Disk (Real.log (23:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert log_23 using 1 <;> norm_num [log23Disk]

def log24Disk : Disk := ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
theorem log24_contains : Contains log24Disk (Real.log (24:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert log_24 using 1 <;> norm_num [log24Disk]

def log25Disk : Disk := ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
theorem log25_contains : Contains log25Disk (Real.log (25:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert log_25 using 1 <;> norm_num [log25Disk]

def log26Disk : Disk := ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
theorem log26_contains : Contains log26Disk (Real.log (26:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert log_26 using 1 <;> norm_num [log26Disk]

def log27Disk : Disk := ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
theorem log27_contains : Contains log27Disk (Real.log (27:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert log_27 using 1 <;> norm_num [log27Disk]

def logpiDisk : Disk := ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
theorem logpi_contains : Contains logpiDisk (Real.log (Real.pi:ℝ) : ℂ) := by
  apply CertifiedScalarExp.contains_real
  convert HardTileLogInputs.log_pi using 1 <;> norm_num [logpiDisk]

end Reinmann.RectangleLogInputs
