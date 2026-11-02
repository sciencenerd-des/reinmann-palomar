/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile016Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨16,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4653/640)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((3/4), (4653/640))
  have he : value ((3/4), (4653/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale (A_variable hcre) S_variable)
  intro k
  fin_cases k <;> norm_num [J_halfVariable, J_variable, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (1, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_base : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_base : Sound J_base F_base c := by
  apply sound_round (sound_add (A_q0 hcre) (A_halfVariable hcre) S_q0 S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_base, J_q0, J_halfVariable, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(12, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (12, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((107/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shift : Sound J_shift F_shift c := by
  apply sound_round (sound_add (A_base hcre) (A_q1 hcre) S_base S_q1)
  intro k
  fin_cases k <;> norm_num [J_shift, J_base, J_q1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftInv : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21913600/314744809), (-5955840/314744809)), 0, by norm_num⟩
  | 1 => ⟨((-222366917427200/99064294792446481), (130513895424000/99064294792446481)), 0, by norm_num⟩
  | 2 => ⟨((4621524157/70368744177664), (-9443618093/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-7437328577/4503599627370496), (6659205269/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((2126327587/72057594037927936), (-2136015277/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((218161181/2305843009213693952), (5080819729/1152921504606846976)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-3319605915/73786976294838206464), (-22507505815/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 7 => ⟨((7105188147/2361183241434822606848), (11531332891/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-2851567597/18889465931478580854784), (-5347205651/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((15944175239/2417851639229258349412352), (4229944395/1208925819614629174706176)), (21/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-10161375467/38685626227668133590597632), (-1149193375/19342813113834066795298816)), (15/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((12015379287/1237940039285380274899124224), (-1032312989/2475880078570760549798248448)), (11/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-826784311/2475880078570760549798248448), (2106405473/19807040628566084398385987584)), (1/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (4653/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (4653/1280)))⁻¹=value ((21913600/314744809), (-5955840/314744809)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/314744809), (-5955840/314744809))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2822889817/1073741824), (2279571247/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((10956800/314744809), (-2977920/314744809)), 0, by norm_num⟩
  | 2 => ⟨((-55591729356800/99064294792446481), (32628473856000/99064294792446481)), 0, by norm_num⟩
  | 3 => ⟨((12324064419/1125899906842624), (-12591490791/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-7437328577/36028797018963968), (6659205269/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((3402124139/1152921504606846976), (-13670497773/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((581763149/73786976294838206464), (27097705221/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-7587670663/2361183241434822606848), (-25722863789/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((7105188147/37778931862957161709568), (11531332891/37778931862957161709568)), (9/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-2534726753/302231454903657293676544), (-2376535845/302231454903657293676544)), (7/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((12755340191/38685626227668133590597632), (845988879/4835703278458516698824704)), (17/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-14780182497/1237940039285380274899124224), (-104472125/38685626227668133590597632)), (23/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((4005126429/9903520314283042199192993792), (-1376417319/79228162514264337593543950336)), (59/79228162514264337593543950336), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (99/20480)), 0, by norm_num⟩
  | 45 => ⟨((103090072217/4080638361600), (-196713/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-48625466814031/1915179604377600), (1345496611987/197568495616000)), 0, by norm_num⟩
  | 43 => ⟨((14224383693/549755813888), (-1892737275/274877906944)), (1/549755813888), by norm_num⟩
  | 42 => ⟨((-14563062623/549755813888), (3852795499/549755813888)), (1/549755813888), by norm_num⟩
  | 41 => ⟨((14922586247/549755813888), (-3940787269/549755813888)), (1/274877906944), by norm_num⟩
  | 40 => ⟨((-15296796061/549755813888), (4036906203/549755813888)), (1/274877906944), by norm_num⟩
  | 39 => ⟨((15688759473/549755813888), (-2068847581/274877906944)), (1/274877906944), by norm_num⟩
  | 38 => ⟨((-8050561167/274877906944), (2121641933/274877906944)), (1/274877906944), by norm_num⟩
  | 37 => ⟨((4133948283/137438953472), (-4354294727/549755813888)), (1/274877906944), by norm_num⟩
  | 36 => ⟨((-16994614535/549755813888), (4471263463/549755813888)), (1/274877906944), by norm_num⟩
  | 35 => ⟨((17479629083/549755813888), (-4594696615/549755813888)), (1/274877906944), by norm_num⟩
  | 34 => ⟨((-17993137783/549755813888), (4725141345/549755813888)), (1/274877906944), by norm_num⟩
  | 33 => ⟨((9268863531/274877906944), (-2431605103/274877906944)), (1/274877906944), by norm_num⟩
  | 32 => ⟨((-19116306969/549755813888), (1252397831/137438953472)), (1/274877906944), by norm_num⟩
  | 31 => ⟨((9866081087/274877906944), (-5165058749/549755813888)), (1/274877906944), by norm_num⟩
  | 30 => ⟨((-5097253607/137438953472), (2665242871/274877906944)), (1/274877906944), by norm_num⟩
  | 29 => ⟨((21091097925/549755813888), (-688357643/68719476736)), (1/274877906944), by norm_num⟩
  | 28 => ⟨((-10921625335/274877906944), (44494603/4294967296)), (1/274877906944), by norm_num⟩
  | 27 => ⟨((707844565/17179869184), (-368569593/34359738368)), (1/274877906944), by norm_num⟩
  | 26 => ⟨((-23520830287/549755813888), (6113746371/549755813888)), (1/274877906944), by norm_num⟩
  | 25 => ⟨((6115023079/137438953472), (-793363105/68719476736)), (1/274877906944), by norm_num⟩
  | 24 => ⟨((-6369369179/137438953472), (3299277583/274877906944)), (1/274877906944), by norm_num⟩
  | 23 => ⟨((6645787881/137438953472), (-3435494251/274877906944)), (1/274877906944), by norm_num⟩
  | 22 => ⟨((-3473641141/68719476736), (3583445445/274877906944)), (1/137438953472), by norm_num⟩
  | 21 => ⟨((3638713033/68719476736), (-1872358047/137438953472)), (1/137438953472), by norm_num⟩
  | 20 => ⟨((-7640505759/137438953472), (1960595045/137438953472)), (1/274877906944), by norm_num⟩
  | 19 => ⟨((8041707773/137438953472), (-2057562141/137438953472)), (1/274877906944), by norm_num⟩
  | 18 => ⟨((-16974735209/274877906944), (4329245611/274877906944)), (1/137438953472), by norm_num⟩
  | 17 => ⟨((8985306687/137438953472), (-2283440141/137438953472)), (1/137438953472), by norm_num⟩
  | 16 => ⟨((-4772647557/68719476736), (302008001/17179869184)), (1/137438953472), by norm_num⟩
  | 15 => ⟨((20359397483/274877906944), (-2565050451/137438953472)), (1/137438953472), by norm_num⟩
  | 14 => ⟨((-21808804963/274877906944), (5467256617/274877906944)), (1/137438953472), by norm_num⟩
  | 13 => ⟨((23480315691/274877906944), (-5851872643/274877906944)), (1/137438953472), by norm_num⟩
  | 12 => ⟨((-25429202075/274877906944), (786842047/34359738368)), (1/137438953472), by norm_num⟩
  | 11 => ⟨((6932683051/68719476736), (-3405087683/137438953472)), (1/137438953472), by norm_num⟩
  | 10 => ⟨((-15245055363/137438953472), (3708820463/137438953472)), (1/68719476736), by norm_num⟩
  | 9 => ⟨((8464751429/68719476736), (-2036056625/68719476736)), (1/137438953472), by norm_num⟩
  | 8 => ⟨((-19032192751/137438953472), (2257208919/68719476736)), (1/137438953472), by norm_num⟩
  | 7 => ⟨((21730941945/137438953472), (-1266177207/34359738368)), (1/137438953472), by norm_num⟩
  | 6 => ⟨((-25321036911/137438953472), (5768139381/137438953472)), (1/68719476736), by norm_num⟩
  | 5 => ⟨((15165758909/68719476736), (-1674801429/34359738368)), (1/68719476736), by norm_num⟩
  | 4 => ⟨((-18906980895/68719476736), (1997581587/34359738368)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((12550364325/34359738368), (-4951070819/68719476736)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-18676478455/34359738368), (3257550985/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((18341870719/17179869184), (-2388843397/17179869184)), (1/17179869184), by norm_num⟩
  | 0 => ⟨((-2466474477/17179869184), (9118284987/34359738368)), (3/68719476736), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (4653/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (4653/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (4653/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((2822889817/1073741824), (2279571247/8589934592)), (1/8589934592), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (4653/1280))) (z:=((-21/128), (4653/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((2822889817/1073741824), (2279571247/8589934592))) (r:=(1/8589934592)) (by norm_num) ?_ hs
  norm_num [J_shiftLog,RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
theorem S_shiftLog : Sound J_shiftLog F_shiftLog c := by
  apply log_coefficients_sound (A_shift hcre) (L_shiftLog hcre) S_shift S_shiftInv
  · exact logValue
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftLog,J_shift,J_shiftInv,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact ((-1/2), 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shiftMinusHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shiftMinusHalf : Sound J_shiftMinusHalf F_shiftMinusHalf c := by
  apply sound_round (sound_add (A_shift hcre) (A_q2 hcre) S_shift S_q2)
  intro k
  fin_cases k <;> norm_num [J_shiftMinusHalf, J_shift, J_q2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainLead : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17654440843/536870912), (1741291317/134217728)), (1/268435456), by norm_num⟩
  | 1 => ⟨((30874022953/17179869184), (590210969/4294967296)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((889944845491200/99064294792446481), (-250635452332320/99064294792446481)), 0, by norm_num⟩
  | 3 => ⟨((-870822119/8796093022208), (8512673769/140737488355328)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((3313432623/2251799813685248), (-7128146055/4503599627370496)), (17/9007199254740992), by norm_num⟩
  | 5 => ⟨((-6375128381/288230376151711744), (3090885163/72057594037927936)), (13/144115188075855872), by norm_num⟩
  | 6 => ⟨((1115861281/4611686018427387904), (-21614543517/18446744073709551616)), (37/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1280894917/590295810358705651712), (18699760955/590295810358705651712)), (99/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-2785066185/9444732965739290427392), (-492008285/590295810358705651712)), (131/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((8850449547/604462909807314587353088), (12626609523/604462909807314587353088)), (47/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-2824990165/4835703278458516698824704), (-9296892463/19342813113834066795298816)), (253/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((6485828337/309485009821345068724781056), (1439473529/154742504910672534362390528)), (327/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-27717162849/39614081257132168796771975168), (-4113373009/39614081257132168796771975168)), (107/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negativeShift : Sound J_negativeShift F_negativeShift c := by
  apply sound_round (sound_scale (A_shift hcre) S_shift)
  intro k
  fin_cases k <;> norm_num [J_negativeShift, J_shift, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainMinusShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10473792395/536870912), (5013555617/536870912)), (5/1073741824), by norm_num⟩
  | 1 => ⟨((22284088361/17179869184), (590210969/4294967296)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((889944845491200/99064294792446481), (-250635452332320/99064294792446481)), 0, by norm_num⟩
  | 3 => ⟨((-870822119/8796093022208), (8512673769/140737488355328)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((3313432623/2251799813685248), (-7128146055/4503599627370496)), (17/9007199254740992), by norm_num⟩
  | 5 => ⟨((-6375128381/288230376151711744), (3090885163/72057594037927936)), (13/144115188075855872), by norm_num⟩
  | 6 => ⟨((1115861281/4611686018427387904), (-21614543517/18446744073709551616)), (37/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1280894917/590295810358705651712), (18699760955/590295810358705651712)), (99/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-2785066185/9444732965739290427392), (-492008285/590295810358705651712)), (131/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((8850449547/604462909807314587353088), (12626609523/604462909807314587353088)), (47/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-2824990165/4835703278458516698824704), (-9296892463/19342813113834066795298816)), (253/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((6485828337/309485009821345068724781056), (1439473529/154742504910672534362390528)), (327/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-27717162849/39614081257132168796771975168), (-4113373009/39614081257132168796771975168)), (107/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainMinusShift : Sound J_mainMinusShift F_mainMinusShift c := by
  apply sound_round (sound_add (A_mainLead hcre) (A_negativeShift hcre) S_mainLead S_negativeShift)
  intro k
  fin_cases k <;> norm_num [J_mainMinusShift, J_mainLead, J_negativeShift, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((31574487577/17179869184), 0), (1/17179869184), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_logTwoPi : Sound J_logTwoPi F_logTwoPi c := by
  apply sound_round (sound_add (A_log2 hcre) (A_logpi hcre) S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [J_logTwoPi, J_log2, J_logpi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_halfLogTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((31574487577/34359738368), 0), (1/34359738368), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfLogTwoPi : Sound J_halfLogTwoPi F_halfLogTwoPi c := by
  apply sound_round (sound_scale (A_logTwoPi hcre) S_logTwoPi)
  intro k
  fin_cases k <;> norm_num [J_halfLogTwoPi, J_logTwoPi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainConstant : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21934287527/1073741824), (5013555617/536870912)), (3/536870912), by norm_num⟩
  | 1 => ⟨((22284088361/17179869184), (590210969/4294967296)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((889944845491200/99064294792446481), (-250635452332320/99064294792446481)), 0, by norm_num⟩
  | 3 => ⟨((-870822119/8796093022208), (8512673769/140737488355328)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((3313432623/2251799813685248), (-7128146055/4503599627370496)), (17/9007199254740992), by norm_num⟩
  | 5 => ⟨((-6375128381/288230376151711744), (3090885163/72057594037927936)), (13/144115188075855872), by norm_num⟩
  | 6 => ⟨((1115861281/4611686018427387904), (-21614543517/18446744073709551616)), (37/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1280894917/590295810358705651712), (18699760955/590295810358705651712)), (99/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-2785066185/9444732965739290427392), (-492008285/590295810358705651712)), (131/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((8850449547/604462909807314587353088), (12626609523/604462909807314587353088)), (47/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-2824990165/4835703278458516698824704), (-9296892463/19342813113834066795298816)), (253/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((6485828337/309485009821345068724781056), (1439473529/154742504910672534362390528)), (327/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-27717162849/39614081257132168796771975168), (-4113373009/39614081257132168796771975168)), (107/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((444733834854400/99064294792446481), (-261027790848000/99064294792446481)), 0, by norm_num⟩
  | 1 => ⟨((-4621524157/17592186044416), (9443618093/35184372088832)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((5577996433/562949953421312), (-19977615807/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-2126327587/9007199254740992), (2136015277/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((-68175369/72057594037927936), (-25404098645/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((622426109/1152921504606846976), (16880629361/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-6217039629/147573952589676412928), (-20179832559/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 7 => ⟨((2851567597/1180591620717411303424), (5347205651/2361183241434822606848)), (5/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-2242149643/18889465931478580854784), (-1189671861/18889465931478580854784)), (9/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((25403438667/4835703278458516698824704), (5745966875/4835703278458516698824704)), (7/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-2065143315/9671406556917033397649408), (177428795/19342813113834066795298816)), (11/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((2480352933/309485009821345068724781056), (-6319216419/2475880078570760549798248448)), (17/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-10936879145/39614081257132168796771975168), (3533600257/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4621524157/17592186044416), (-9443618093/35184372088832)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-5577996433/281474976710656), (19977615807/562949953421312)), (1/281474976710656), by norm_num⟩
  | 2 => ⟨((3189491381/4503599627370496), (-25632183325/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((68175369/18014398509481984), (25404098645/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((-3112130545/1152921504606846976), (-10550393351/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 5 => ⟨((9325559443/36893488147419103232), (3783718605/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-4990243295/295147905179352825856), (-9357609889/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((2242149643/2361183241434822606848), (1189671861/2361183241434822606848)), (15/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-7144717125/151115727451828646838272), (-3232106367/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((20651433149/9671406556917033397649408), (-887143975/9671406556917033397649408)), (11/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-13641941131/154742504910672534362390528), (543057661/19342813113834066795298816)), (19/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((8202659359/2475880078570760549798248448), (-10600800771/4951760157141521099596496896)), (15/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-4394121573/39614081257132168796771975168), (611623571/4951760157141521099596496896)), (25/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7437328577/562949953421312), (-6659205269/281474976710656)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((-4252655175/4503599627370496), (2136015277/562949953421312)), (3/4503599627370496), by norm_num⟩
  | 2 => ⟨((-545402951/72057594037927936), (-12702049323/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 3 => ⟨((4149507393/576460752303423488), (14067191135/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 4 => ⟨((-485706221/576460752303423488), (-6306197675/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((4990243295/73786976294838206464), (4678804945/73786976294838206464)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-20926730001/4722366482869645213696), (-11103604037/4722366482869645213696)), (15/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((19052579001/75557863725914323419136), (1077368789/18889465931478580854784)), (1/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-7744287431/604462909807314587353088), (665357981/1208925819614629174706176)), (15/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((2842071069/4835703278458516698824704), (-7240768813/38685626227668133590597632)), (27/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-1879776103/77371252455336267181195264), (9717400707/618970019642690137449562112)), (25/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((4394121573/4951760157141521099596496896), (-611623571/618970019642690137449562112)), (21/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-8533791637/316912650057057350374175801344), (16952613737/316912650057057350374175801344)), (9/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2126327587/4503599627370496), (-2136015277/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((545402951/72057594037927936), (25404098645/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 2 => ⟨((-3112130545/288230376151711744), (-21100786703/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 3 => ⟨((485706221/288230376151711744), (6306197675/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-12475608237/73786976294838206464), (-5848506181/36893488147419103232)), (9/73786976294838206464), by norm_num⟩
  | 5 => ⟨((15695047501/1180591620717411303424), (2081925757/295147905179352825856)), (3/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-8335503313/9444732965739290427392), (-1885395381/9444732965739290427392)), (13/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((30977149725/604462909807314587353088), (-665357981/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-12789319811/4835703278458516698824704), (8145864915/9671406556917033397649408)), (15/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((18797761031/154742504910672534362390528), (-3036687721/38685626227668133590597632)), (29/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((-6041917163/1237940039285380274899124224), (6727859281/1237940039285380274899124224)), (27/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((400021483/2475880078570760549798248448), (-12714460303/39614081257132168796771975168)), (25/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-1093445089/316912650057057350374175801344), (21468500545/1267650600228229401496703205376)), (11/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-218161181/72057594037927936), (-5080819729/36028797018963968)), (7/144115188075855872), by norm_num⟩
  | 1 => ⟨((622426109/72057594037927936), (16880629361/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 2 => ⟨((-9325559443/4611686018427387904), (-15134874421/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((4990243295/18446744073709551616), (4678804945/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-15695047501/590295810358705651712), (-2081925757/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 5 => ⟨((20005207951/9444732965739290427392), (2262474457/4722366482869645213696)), (17/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-2710500601/18889465931478580854784), (931501173/151115727451828646838272)), (5/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((10231455849/1208925819614629174706176), (-1629172983/604462909807314587353088)), (3/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-528687029/1208925819614629174706176), (10932075795/38685626227668133590597632)), (13/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((12083834327/618970019642690137449562112), (-13455718563/618970019642690137449562112)), (27/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-7040378101/9903520314283042199192993792), (13985906333/9903520314283042199192993792)), (27/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((5248536427/316912650057057350374175801344), (-12881100327/158456325028528675187087900672)), (51/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((1383471467/5070602400912917605986812821504), (21453642801/5070602400912917605986812821504)), (47/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3319605915/1152921504606846976), (-22507505815/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 1 => ⟨((12434079257/9223372036854775808), (20179832559/9223372036854775808)), (11/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-4990243295/18446744073709551616), (-4678804945/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 3 => ⟨((10463365001/295147905179352825856), (5551802019/295147905179352825856)), (17/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-8335503313/2361183241434822606848), (-1885395381/2361183241434822606848)), (15/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((2710500601/9444732965739290427392), (-931501173/75557863725914323419136)), (11/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-23873396981/1208925819614629174706176), (3801403627/604462909807314587353088)), (29/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((11278656619/9671406556917033397649408), (-3644025265/4835703278458516698824704)), (9/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-9062875745/154742504910672534362390528), (5045894461/77371252455336267181195264)), (21/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((5866981751/2475880078570760549798248448), (-11654921945/2475880078570760549798248448)), (23/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-601394799/9903520314283042199192993792), (2951918825/9903520314283042199192993792)), (47/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-1383471467/1267650600228229401496703205376), (-21453642801/1267650600228229401496703205376)), (3/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((6027408863/20282409603651670423947251286016), (8804977219/10141204801825835211973625643008)), (47/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7105188147/18446744073709551616), (-11531332891/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 1 => ⟨((2851567597/18446744073709551616), (5347205651/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-2242149643/73786976294838206464), (-9517374889/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 3 => ⟨((19052579001/4722366482869645213696), (4309475157/4722366482869645213696)), (9/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-15488574863/37778931862957161709568), (665357981/37778931862957161709568)), (33/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((10231455849/302231454903657293676544), (-6516691931/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-11278656619/4835703278458516698824704), (3644025265/2417851639229258349412352)), (19/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((1294696535/9671406556917033397649408), (-5766736527/38685626227668133590597632)), (13/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-7543262251/1237940039285380274899124224), (14984899643/1237940039285380274899124224)), (31/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((859135427/4951760157141521099596496896), (-4217026893/4951760157141521099596496896)), (9/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((67938331/19807040628566084398385987584), (8428216815/158456325028528675187087900672)), (5/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-2583175227/2535301200456458802993406410752), (-7547123331/2535301200456458802993406410752)), (21/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((8174099019/81129638414606681695789005144064), (3018311475/20282409603651670423947251286016)), (43/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2851567597/73786976294838206464), (-5347205651/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 1 => ⟨((17937197143/1180591620717411303424), (1189671861/147573952589676412928)), (9/590295810358705651712), by norm_num⟩
  | 2 => ⟨((-14289434251/4722366482869645213696), (-3232106367/4722366482869645213696)), (15/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((30977149725/75557863725914323419136), (-1330715961/75557863725914323419136)), (35/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-25578639623/604462909807314587353088), (8145864915/604462909807314587353088)), (9/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((16917984929/4835703278458516698824704), (-10932075795/4835703278458516698824704)), (31/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((-9062875745/38685626227668133590597632), (5045894461/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((7543262251/618970019642690137449562112), (-14984899643/618970019642690137449562112)), (17/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-1933054711/4951760157141521099596496896), (9488310509/4951760157141521099596496896)), (43/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-339691655/39614081257132168796771975168), (-21070542037/158456325028528675187087900672)), (53/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((7103731875/2535301200456458802993406410752), (2594323645/316912650057057350374175801344)), (61/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-12261148529/40564819207303340847894502572032), (-9054934425/20282409603651670423947251286016)), (17/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((15951351695/649037107316853453566312041152512), (6859037839/324518553658426726783156020576256)), (73/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-15944175239/4722366482869645213696), (-4229944395/2361183241434822606848)), (21/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((12701719333/9444732965739290427392), (5745966875/18889465931478580854784)), (15/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((-10325716575/37778931862957161709568), (887143975/75557863725914323419136)), (27/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((22736568553/604462909807314587353088), (-7240768813/604462909807314587353088)), (17/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((-2349720129/604462909807314587353088), (3036687721/1208925819614629174706176)), (37/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((12083834327/38685626227668133590597632), (-13455718563/38685626227668133590597632)), (35/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-5866981751/309485009821345068724781056), (1456865243/38685626227668133590597632)), (29/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((859135427/1237940039285380274899124224), (-4217026893/1237940039285380274899124224)), (43/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((1358766619/79228162514264337593543950336), (21070542037/79228162514264337593543950336)), (29/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((-986629427/158456325028528675187087900672), (-11530327311/633825300114114700748351602688)), (37/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((7492924101/10141204801825835211973625643008), (11067142075/10141204801825835211973625643008)), (45/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((-10634234463/162259276829213363391578010288128), (-9145383785/162259276829213363391578010288128)), (13/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((3197065627/649037107316853453566312041152512), (6097049765/2596148429267413814265248164610048)), (29/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10161375467/37778931862957161709568), (-1149193375/18889465931478580854784)), (15/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((16521146519/151115727451828646838272), (-709715179/151115727451828646838272)), (25/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-3410485283/151115727451828646838272), (543057661/75557863725914323419136)), (3/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((15038208825/4835703278458516698824704), (-9717400707/4835703278458516698824704)), (1/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-12083834327/38685626227668133590597632), (13455718563/38685626227668133590597632)), (37/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((7040378101/309485009821345068724781056), (-6992953167/154742504910672534362390528)), (37/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((-601394799/618970019642690137449562112), (2951918825/618970019642690137449562112)), (65/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((-67938331/2475880078570760549798248448), (-8428216815/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((3551865937/316912650057057350374175801344), (2594323645/79228162514264337593543950336)), (37/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((-7492924101/5070602400912917605986812821504), (-11067142075/5070602400912917605986812821504)), (25/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((5848828955/40564819207303340847894502572032), (2514980541/20282409603651670423947251286016)), (63/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((-7672957505/649037107316853453566312041152512), (-3658229859/649037107316853453566312041152512)), (19/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((8850469445/10384593717069655257060992658440192), (3212141849/20769187434139310514121985316880384)), (11/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/944234427), (-496320/314744809)), 0, by norm_num⟩
  | 1 => ⟨((-55591729356800/297192884377339443), (10876157952000/99064294792446481)), 0, by norm_num⟩
  | 2 => ⟨((12324064419/2251799813685248), (-12591490791/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-9916438103/72057594037927936), (17757880717/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((5670206899/2305843009213693952), (-22784162955/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 5 => ⟨((581763149/73786976294838206464), (27097705221/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-1106535305/295147905179352825856), (-15005003877/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 7 => ⟨((2368396049/9444732965739290427392), (15375110521/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-15208360517/1208925819614629174706176), (-14259215069/1208925819614629174706176)), (5/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((21258900319/38685626227668133590597632), (1409981465/4835703278458516698824704)), (29/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-27097001245/1237940039285380274899124224), (-6129031333/1237940039285380274899124224)), (41/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((4005126429/4951760157141521099596496896), (-1376417319/39614081257132168796771975168)), (59/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-17638065301/633825300114114700748351602688), (5617081261/633825300114114700748351602688)), (11/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10970258661/536870912), (5012709027/536870912)), (7/1073741824), by norm_num⟩
  | 1 => ⟨((11140437381/8589934592), (2362730035/17179869184)), (3/17179869184), by norm_num⟩
  | 2 => ⟨((19766977355/2199023255552), (-5575887069/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-13952521947/140737488355328), (4273678565/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((6637939869/4503599627370496), (-14345292747/9007199254740992)), (9/4503599627370496), by norm_num⟩
  | 5 => ⟨((-6372855869/288230376151711744), (12469391063/288230376151711744)), (27/288230376151711744), by norm_num⟩
  | 6 => ⟨((4394286667/18446744073709551616), (-21848996703/18446744073709551616)), (75/18446744073709551616), by norm_num⟩
  | 7 => ⟨((714459835/295147905179352825856), (18939997057/590295810358705651712)), (25/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5807763003/18889465931478580854784), (-15967065355/18889465931478580854784)), (33/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1147827483/75557863725914323419136), (6401428603/302231454903657293676544)), (95/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-1465418913/2417851639229258349412352), (-4696329289/9671406556917033397649408)), (255/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((6736148739/309485009821345068724781056), (5736387595/618970019642690137449562112)), (329/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-14409770965/19807040628566084398385987584), (-1881152715/19807040628566084398385987584)), (215/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-13145668713/18014398509481984), (6715461755/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((3966575241/72057594037927936), (-7103152287/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 2 => ⟨((-283510345/144115188075855872), (4556832591/576460752303423488)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((-387842099/36893488147419103232), (-9032568407/18446744073709551616)), (5/36893488147419103232), by norm_num⟩
  | 4 => ⟨((1106535305/147573952589676412928), (15005003877/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-6631508937/9444732965739290427392), (-10762577365/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((14194469817/302231454903657293676544), (13308600731/302231454903657293676544)), (3/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-12755340191/4835703278458516698824704), (-6767911031/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((20322750933/154742504910672534362390528), (1149193375/38685626227668133590597632)), (5/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-29370927145/4951760157141521099596496896), (315428969/1237940039285380274899124224)), (1/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((19401871831/79228162514264337593543950336), (-6178789387/79228162514264337593543950336)), (7/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-5833002211/633825300114114700748351602688), (7538347215/1267650600228229401496703205376)), (11/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((12498834697/40564819207303340847894502572032), (-13917834149/40564819207303340847894502572032)), (37/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10970258269/536870912), (10025418855/1073741824)), (1/134217728), by norm_num⟩
  | 1 => ⟨((5570218927/4294967296), (2362728341/17179869184)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((19766973029/2199023255552), (-2787934843/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-13952523427/140737488355328), (8547288217/140737488355328)), (7/140737488355328), by norm_num⟩
  | 4 => ⟨((3318986819/2251799813685248), (-14345063789/9007199254740992)), (19/9007199254740992), by norm_num⟩
  | 5 => ⟨((-6373058247/288230376151711744), (12469062615/288230376151711744)), (7/72057594037927936), by norm_num⟩
  | 6 => ⟨((4395153029/18446744073709551616), (-10924092205/9223372036854775808)), (19/4611686018427387904), by norm_num⟩
  | 7 => ⟨((713681311/295147905179352825856), (1183698181/36893488147419103232)), (101/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-2902641099/9444732965739290427392), (-15966504225/18889465931478580854784)), (133/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((4589517273/302231454903657293676544), (1600376403/75557863725914323419136)), (191/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-11718614519/19342813113834066795298816), (-293567721/604462909807314587353088)), (1/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((13466601187/618970019642690137449562112), (5740068429/618970019642690137449562112)), (165/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-28807336037/39614081257132168796771975168), (-3775897065/39614081257132168796771975168)), (861/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1728063055/4611686018427387904), (-13887489801/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 1 => ⟨((443248113/73786976294838206464), (20645870645/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-1264611777/147573952589676412928), (-4287143965/147573952589676412928)), (3/295147905179352825856), by norm_num⟩
  | 3 => ⟨((12631445595/9444732965739290427392), (20500147363/9444732965739290427392)), (3/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-2534726753/18889465931478580854784), (-2376535845/18889465931478580854784)), (1/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((12755340191/1208925819614629174706176), (845988879/151115727451828646838272)), (11/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-13548500623/19342813113834066795298816), (-3064515667/19342813113834066795298816)), (11/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((25175080411/618970019642690137449562112), (-540735375/309485009821345068724781056)), (3/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-5196929955/2475880078570760549798248448), (3310065743/4951760157141521099596496896)), (13/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((1909613819/19807040628566084398385987584), (-9871645163/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((-613782061/158456325028528675187087900672), (10935441117/2535301200456458802993406410752)), (23/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((10403098377/81129638414606681695789005144064), (-20666043413/81129638414606681695789005144064)), (41/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-3554564353/1298074214633706907132624082305024), (4361854079/324518553658426726783156020576256)), (37/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10970258269/536870912), (10025418853/1073741824)), (9/1073741824), by norm_num⟩
  | 1 => ⟨((5570218927/4294967296), (1181364173/8589934592)), (5/17179869184), by norm_num⟩
  | 2 => ⟨((9883486505/1099511627776), (-2787934875/1099511627776)), (3/2199023255552), by norm_num⟩
  | 3 => ⟨((-13952523239/140737488355328), (4273644261/70368744177664)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((13275946067/9007199254740992), (-7172532461/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((-3186527603/144115188075855872), (12469064229/288230376151711744)), (29/288230376151711744), by norm_num⟩
  | 6 => ⟨((1098785027/4611686018427387904), (-21848187333/18446744073709551616)), (77/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1427386631/590295810358705651712), (18939169865/590295810358705651712)), (51/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-5805321847/18889465931478580854784), (-7983245799/9444732965739290427392)), (67/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((9179092823/604462909807314587353088), (12802973567/604462909807314587353088)), (3/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-2929672361/4835703278458516698824704), (-9394083641/19342813113834066795298816)), (257/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((3366670139/154742504910672534362390528), (717488845/77371252455336267181195264)), (331/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-14403722257/19807040628566084398385987584), (-943841153/9903520314283042199192993792)), (431/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4046757687/2361183241434822606848), (13718860687/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-7578867357/9444732965739290427392), (-12300088417/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((6083344207/37778931862957161709568), (1425921507/9444732965739290427392)), (11/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-398604381/18889465931478580854784), (-6767911033/604462909807314587353088)), (11/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((20322750935/9671406556917033397649408), (1149193375/2417851639229258349412352)), (5/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-26433834433/154742504910672534362390528), (1135544287/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((7275701937/618970019642690137449562112), (-4634092041/1237940039285380274899124224)), (19/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-13749219497/19807040628566084398385987584), (4442240323/9903520314283042199192993792)), (23/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((11048077099/316912650057057350374175801344), (-12302371257/316912650057057350374175801344)), (27/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((-7152130135/5070602400912917605986812821504), (14207904847/5070602400912917605986812821504)), (29/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((2932515591/81129638414606681695789005144064), (-14394118461/81129638414606681695789005144064)), (15/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((843258799/1298074214633706907132624082305024), (1634563261/162259276829213363391578010288128)), (15/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-7347698423/41538374868278621028243970633760768), (-21467373029/41538374868278621028243970633760768)), (29/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10970258269/536870912), (10025418853/1073741824)), (5/536870912), by norm_num⟩
  | 1 => ⟨((5570218927/4294967296), (1181364173/8589934592)), (3/8589934592), by norm_num⟩
  | 2 => ⟨((9883486505/1099511627776), (-2787934875/1099511627776)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-6976261621/70368744177664), (1068411065/17592186044416)), (9/140737488355328), by norm_num⟩
  | 4 => ⟨((6637973043/4503599627370496), (-7172532459/4503599627370496)), (21/9007199254740992), by norm_num⟩
  | 5 => ⟨((-6373055255/288230376151711744), (12469064231/288230376151711744)), (15/144115188075855872), by norm_num⟩
  | 6 => ⟨((4395140325/18446744073709551616), (-10924093701/9223372036854775808)), (39/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1427386221/590295810358705651712), (9469585065/295147905179352825856)), (103/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-1451330297/4722366482869645213696), (-15966492331/18889465931478580854784)), (135/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((4589545985/302231454903657293676544), (12802975261/604462909807314587353088)), (193/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-11718688745/19342813113834066795298816), (-9394087073/19342813113834066795298816)), (129/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((6733340479/309485009821345068724781056), (5739916995/618970019642690137449562112)), (83/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-28807451521/39614081257132168796771975168), (-3775385085/39614081257132168796771975168)), (863/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9831667405/302231454903657293676544), (-9218078429/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((15461018413/1208925819614629174706176), (8203528523/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((-24633637497/9671406556917033397649408), (-2785923333/4835703278458516698824704)), (27/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((26700842861/77371252455336267181195264), (-1147014431/77371252455336267181195264)), (31/77371252455336267181195264), by norm_num⟩
  | 4 => ⟨((-5511895407/154742504910672534362390528), (7021351577/618970019642690137449562112)), (1/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((1822813191/618970019642690137449562112), (-9422934019/4951760157141521099596496896)), (7/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-3905885843/19807040628566084398385987584), (17397292687/79228162514264337593543950336)), (21/39614081257132168796771975168), by norm_num⟩
  | 7 => ⟨((3250968243/316912650057057350374175801344), (-12916277133/633825300114114700748351602688)), (15/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((-3332404081/10141204801825835211973625643008), (16356952797/10141204801825835211973625643008)), (19/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-1171192777/162259276829213363391578010288128), (-4540453503/40564819207303340847894502572032)), (47/162259276829213363391578010288128), by norm_num⟩
  | 10 => ⟨((1530770505/649037107316853453566312041152512), (17889477525/2596148429267413814265248164610048)), (53/2596148429267413814265248164610048), by norm_num⟩
  | 11 => ⟨((-10568532065/41538374868278621028243970633760768), (-15609853285/41538374868278621028243970633760768)), (15/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((6874656623/332306998946228968225951765070086144), (11824334591/664613997892457936451903530140172288)), (1/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10970258269/536870912), (10025418853/1073741824)), (11/1073741824), by norm_num⟩
  | 1 => ⟨((5570218927/4294967296), (1181364173/8589934592)), (7/17179869184), by norm_num⟩
  | 2 => ⟨((9883486505/1099511627776), (-2787934875/1099511627776)), (5/2199023255552), by norm_num⟩
  | 3 => ⟨((-6976261621/70368744177664), (1068411065/17592186044416)), (5/70368744177664), by norm_num⟩
  | 4 => ⟨((6637973043/4503599627370496), (-7172532459/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((-3186527627/144115188075855872), (6234532115/144115188075855872)), (31/288230376151711744), by norm_num⟩
  | 6 => ⟨((4395140321/18446744073709551616), (-10924093699/9223372036854775808)), (79/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1427386227/590295810358705651712), (9469585059/295147905179352825856)), (13/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2902660597/9444732965739290427392), (-15966492301/18889465931478580854784)), (17/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((4589545983/302231454903657293676544), (12802975193/604462909807314587353088)), (97/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-11718688699/19342813113834066795298816), (-2348521735/4835703278458516698824704)), (259/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((13466680801/618970019642690137449562112), (2869958381/309485009821345068724781056)), (333/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-28807450701/39614081257132168796771975168), (-943846095/9903520314283042199192993792)), (27/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19952344041/38685626227668133590597632), (4512991703/38685626227668133590597632)), (15/19342813113834066795298816), by norm_num⟩
  | 1 => ⟨((-16220028497/77371252455336267181195264), (1393559511/154742504910672534362390528)), (25/77371252455336267181195264), by norm_num⟩
  | 2 => ⟨((1674162517/38685626227668133590597632), (-1066319547/77371252455336267181195264)), (25/309485009821345068724781056), by norm_num⟩
  | 3 => ⟨((-14764119149/2475880078570760549798248448), (9540289241/2475880078570760549798248448)), (1/77371252455336267181195264), by norm_num⟩
  | 4 => ⟨((5931795863/9903520314283042199192993792), (-3302617925/4951760157141521099596496896)), (37/19807040628566084398385987584), by norm_num⟩
  | 5 => ⟨((-6912058633/158456325028528675187087900672), (13730996153/158456325028528675187087900672)), (37/158456325028528675187087900672), by norm_num⟩
  | 6 => ⟨((4723469169/2535301200456458802993406410752), (-11592466033/1267650600228229401496703205376)), (65/2535301200456458802993406410752), by norm_num⟩
  | 7 => ⟨((533600577/10141204801825835211973625643008), (1034325287/1267650600228229401496703205376)), (13/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((-6974257707/324518553658426726783156020576256), (-20376311489/324518553658426726783156020576256)), (37/162259276829213363391578010288128), by norm_num⟩
  | 9 => ⟨((7356356431/2596148429267413814265248164610048), (1358178741/324518553658426726783156020576256)), (25/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((-2871113461/10384593717069655257060992658440192), (-9876567827/41538374868278621028243970633760768)), (63/41538374868278621028243970633760768), by norm_num⟩
  | 11 => ⟨((7533108507/332306998946228968225951765070086144), (7183108327/664613997892457936451903530140172288)), (19/166153499473114484112975882535043072), by norm_num⟩
  | 12 => ⟨((-17378317715/10633823966279326983230456482242756608), (-3153596651/10633823966279326983230456482242756608)), (87/10633823966279326983230456482242756608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10970258269/536870912), (10025418853/1073741824)), (3/268435456), by norm_num⟩
  | 1 => ⟨((5570218927/4294967296), (1181364173/8589934592)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((9883486505/1099511627776), (-2787934875/1099511627776)), (3/1099511627776), by norm_num⟩
  | 3 => ⟨((-6976261621/70368744177664), (1068411065/17592186044416)), (11/140737488355328), by norm_num⟩
  | 4 => ⟨((6637973043/4503599627370496), (-7172532459/4503599627370496)), (23/9007199254740992), by norm_num⟩
  | 5 => ⟨((-3186527627/144115188075855872), (6234532115/144115188075855872)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((4395140321/18446744073709551616), (-10924093699/9223372036854775808)), (5/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1427386227/590295810358705651712), (9469585059/295147905179352825856)), (105/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-2902660597/9444732965739290427392), (-7983246151/9444732965739290427392)), (137/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((8963957/590295810358705651712), (3200743799/151115727451828646838272)), (195/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-183104511/302231454903657293676544), (-9394086945/19342813113834066795298816)), (65/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((13466680815/618970019642690137449562112), (5739916769/618970019642690137449562112)), (167/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-14403725383/19807040628566084398385987584), (-471923049/4951760157141521099596496896)), (865/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1563843232695509/2097152), (137783950107707/2097152)), (47162767/2097152), by norm_num⟩
  | 1 => ⟨((-3904581407/4), (-555102335/32)), (1045/32), by norm_num⟩
  | 2 => ⟨((-10213339135/16), (-1214263879/16)), (383/16), by norm_num⟩
  | 3 => ⟨((-17810266169/64), (-3876935605/64)), (757/64), by norm_num⟩
  | 4 => ⟨((-2913227613/32), (-3684179601/128)), (567/128), by norm_num⟩
  | 5 => ⟨((-12208449225/512), (-1270136945/128)), (687/512), by norm_num⟩
  | 6 => ⟨((-21335249011/4096), (-5541074171/2048)), (175/512), by norm_num⟩
  | 7 => ⟨((-15990567429/16384), (-2509976715/4096)), (1235/16384), by norm_num⟩
  | 8 => ⟨((-2622752453/16384), (-7800581511/65536)), (241/16384), by norm_num⟩
  | 9 => ⟨((-12235776767/524288), (-10632404617/524288)), (675/262144), by norm_num⟩
  | 10 => ⟨((-3208786601/1048576), (-3231780225/1048576)), (1719/4194304), by norm_num⟩
  | 11 => ⟨((-6110846467/16777216), (-14203074931/33554432)), (1005/16777216), by norm_num⟩
  | 12 => ⟨((-5320212671/134217728), (-14248696247/268435456)), (17/2097152), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1610592940641265/10141204801825835211973625643008), (994450725161/2535301200456458802993406410752)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((907049954565055/316912650057057350374175801344), (1220598334063/158456325028528675187087900672)), (4489/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1929531445143605/39614081257132168796771975168), (688416369613/4951760157141521099596496896)), (20265/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((965916496403119/1237940039285380274899124224), (5864034704107/2475880078570760549798248448)), (21585/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((226692966102249/19342813113834066795298816), (1469504048133/38685626227668133590597632)), (5411/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((794653381045673/4835703278458516698824704), (2762769893363/4835703278458516698824704)), (20355/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((646810161051163/302231454903657293676544), (2424899839965/302231454903657293676544)), (8937/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1944482692884829/75557863725914323419136), (3954536428119/37778931862957161709568)), (7291/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1340135751875581/4722366482869645213696), (1489136922587/1180591620717411303424)), (10989/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((52504553731871/18446744073709551616), (8230673940351/590295810358705651712)), (3799/73786976294838206464), by norm_num⟩
  | 8 => ⟨((948519466264253/36893488147419103232), (5174674732511/36893488147419103232)), (38249/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1905682410385347/9223372036854775808), (11727517686021/9223372036854775808)), (21695/4611686018427387904), by norm_num⟩
  | 6 => ⟨((419316220317635/288230376151711744), (2958517985717/288230376151711744)), (10961/288230376151711744), by norm_num⟩
  | 5 => ⟨((79239264635645/9007199254740992), (10475977381451/144115188075855872)), (38881/144115188075855872), by norm_num⟩
  | 4 => ⟨((1602271864316961/36028797018963968), (7979779826105/18014398509481984)), (29687/18014398509481984), by norm_num⟩
  | 3 => ⟨((814450727010001/4503599627370496), (10193344132097/4503599627370496)), (76093/9007199254740992), by norm_num⟩
  | 2 => ⟨((627837113279163/1125899906842624), (21057710727493/2251799813685248)), (78983/2251799813685248), by norm_num⟩
  | 1 => ⟨((331462797325177/281474976710656), (33318409062187/1125899906842624)), (125967/1125899906842624), by norm_num⟩
  | 0 => ⟨((1547623319051007/1125899906842624), (73899814315179/1125899906842624)), (70893/281474976710656), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1547623319051007/1125899906842624), (73899814315179/1125899906842624)), (270435334325694949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1061229661975921/562949953421312), (50790072551137/281474976710656)), (204201/281474976710656), by norm_num⟩
  | 2 => ⟨((247777325230409/70368744177664), (95745512007951/140737488355328)), (421791/140737488355328), by norm_num⟩
  | 3 => ⟨((209971780872279/17592186044416), (84283040522401/17592186044416)), (886065/35184372088832), by norm_num⟩
  | 4 => ⟨((1051163219556647/8796093022208), (1005961400768399/8796093022208)), (3705181/4398046511104), by norm_num⟩
  | 5 => ⟨((41293979041857/34359738368), (469593086541231/17179869184)), (6769713/17179869184), by norm_num⟩
  | 6 => ⟨((-1563843232695509/2097152), (137783950107707/2097152)), (47162767/2097152), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((10970258269/536870912), (10025418853/1073741824)), (3/268435456), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem gammaExpValue_checks : CertifiedScalarExp.Checks gammaExpValue := by
  constructor
  · norm_num [gammaExpValue, CertifiedScalarExp.reduced, gammaExpValuePoly, gammaExpValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        gammaExpValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue, gammaExpValueSquares, gammaExpValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, gammaExpValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_gammaExp : Sound J_gammaExp F_gammaExp c := by
  apply exp_sound (A_mainCorr6 hcre) S_mainCorr6 gammaExpValue gammaExpValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue,J_mainCorr6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaExp,J_mainCorr6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((204800/2249819), (-541440/2249819)), 0, by norm_num⟩
  | 1 => ⟨((11418828800/460153230251), (110886912000/5061685532761)), 0, by norm_num⟩
  | 2 => ⟨((-42881473576960000/11387876283630820259), (22649538871296000/11387876283630820259)), 0, by norm_num⟩
  | 3 => ⟨((-2390361145/35184372088832), (-19127315459/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((19283043915/281474976710656), (2331776083/140737488355328)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-11510616771/2251799813685248), (16864495879/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((-12043170289/18014398509481984), (-17221220197/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 7 => ⟨((20962928553/144115188075855872), (-1330661811/36028797018963968)), (9/144115188075855872), by norm_num⟩
  | 8 => ⟨((-2509203885/1152921504606846976), (22117772481/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-10188874551/4611686018427387904), (-10468936667/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 10 => ⟨((17497699299/73786976294838206464), (-15804454037/73786976294838206464)), (13/36893488147419103232), by norm_num⟩
  | 11 => ⟨((4421364365/295147905179352825856), (22598629481/590295810358705651712)), (9/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-12487042549/2361183241434822606848), (35471237/590295810358705651712)), (49/4722366482869645213696), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (4653/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (4653/1280)))⁻¹=value ((204800/2249819), (-541440/2249819)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((204800/2249819), (-541440/2249819))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor1 : Sound J_gammaFactor1 F_gammaFactor1 c := by
  apply sound_round (sound_add (A_base hcre) (A_q0 hcre) S_base S_q0)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor1, J_base, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3891200/30892009), (-5955840/30892009)), 0, by norm_num⟩
  | 1 => ⟨((10165296332800/954316220056081), (23175364608000/954316220056081)), 0, by norm_num⟩
  | 2 => ⟨((-13246316015/4398046511104), (-4421372127/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((8378938043/35184372088832), (-9101475681/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((5594407073/562949953421312), (11047423497/281474976710656)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((-19857864255/4503599627370496), (-1704520907/1125899906842624)), (9/4503599627370496), by norm_num⟩
  | 6 => ⟨((15263278809/36028797018963968), (-5939382915/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 7 => ⟨((1470355415/288230376151711744), (4438957015/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 8 => ⟨((-14433806229/2305843009213693952), (-7812282659/2305843009213693952)), (21/2305843009213693952), by norm_num⟩
  | 9 => ⟨((831068743/1152921504606846976), (-3597453711/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-2302202531/295147905179352825856), (27759210651/295147905179352825856)), (9/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-5061862007/590295810358705651712), (-7880885339/1180591620717411303424)), (47/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((11178389469/9444732965739290427392), (-1918242313/4722366482869645213696)), (121/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (4653/1280)))⁻¹=value ((3891200/30892009), (-5955840/30892009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/30892009), (-5955840/30892009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2427812249600/69501428796371), (-3326607360000/69501428796371)), 0, by norm_num⟩
  | 1 => ⟨((15572777411/1099511627776), (-2614279523/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-1657346213/2199023255552), (21916069633/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-2692324797/8796093022208), (-5012919889/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((16485840379/281474976710656), (-6383871331/281474976710656)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((-395421161/562949953421312), (10136768847/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 6 => ⟨((-19674809693/18014398509481984), (-5640918641/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 7 => ⟨((10113875423/72057594037927936), (-7100280637/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 8 => ⟨((4707699229/1152921504606846976), (13011956905/576460752303423488)), (23/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-27026299045/9223372036854775808), (-1717870739/2305843009213693952)), (33/9223372036854775808), by norm_num⟩
  | 10 => ⟨((4518312483/18446744073709551616), (-5686064175/18446744073709551616)), (3/4611686018427387904), by norm_num⟩
  | 11 => ⟨((869036921/36893488147419103232), (13269536075/295147905179352825856)), (1/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-3820409979/590295810358705651712), (2202012209/4722366482869645213696)), (87/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct1 : Sound J_gammaProduct1 F_gammaProduct1 c := by
  apply sound_round (sound_mul (A_gammaInverse0 hcre) (A_gammaInverse1 hcre) S_gammaInverse0 S_gammaInverse1)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct1, J_gammaInverse0, J_gammaInverse1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (2, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((27/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor2 : Sound J_gammaFactor2 F_gammaFactor2 c := by
  apply sound_round (sound_add (A_base hcre) (A_q3 hcre) S_base S_q3)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor2, J_base, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((204800/1493067), (-661760/4479201)), 0, by norm_num⟩
  | 1 => ⟨((30219468800/20063241598401), (135528448000/6687747199467)), 0, by norm_num⟩
  | 2 => ⟨((-14076363421/8796093022208), (-5623326633/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((28739238005/140737488355328), (-536977575/17592186044416)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-6614834025/562949953421312), (2417599737/140737488355328)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-2085487285/4503599627370496), (-18429939943/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((6589944873/36028797018963968), (1911763051/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((-23501044095/1152921504606846976), (3593118473/576460752303423488)), (19/1152921504606846976), by norm_num⟩
  | 8 => ⟨((8647504169/9223372036854775808), (-17831104181/9223372036854775808)), (23/9223372036854775808), by norm_num⟩
  | 9 => ⟨((5792894707/73786976294838206464), (7446865085/36893488147419103232)), (27/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-11980019995/590295810358705651712), (-74192945/9223372036854775808)), (63/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((18758330113/9444732965739290427392), (-8948940181/9444732965739290427392)), (73/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-5003631109/75557863725914323419136), (1999434875/9444732965739290427392)), (21/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (4653/1280)))⁻¹=value ((204800/1493067), (-661760/4479201)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((204800/1493067), (-661760/4479201))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-26086890603/2199023255552), (-1544272599/1099511627776)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((11033935863/4398046511104), (-14067749277/4398046511104)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((1446720939/4398046511104), (15090788493/17592186044416)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-5981713865/35184372088832), (-1998319247/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((5190609915/281474976710656), (-6298047677/281474976710656)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((3652251921/2251799813685248), (9537547261/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((-12005738331/18014398509481984), (-857672829/9007199254740992)), (7/18014398509481984), by norm_num⟩
  | 7 => ⟨((8277471313/144115188075855872), (-11090097843/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 8 => ⟨((6502770183/1152921504606846976), (13850583559/1152921504606846976)), (1/72057594037927936), by norm_num⟩
  | 9 => ⟨((-16475368575/9223372036854775808), (-706156487/9223372036854775808)), (23/9223372036854775808), by norm_num⟩
  | 10 => ⟨((8575649033/73786976294838206464), (-15138801461/73786976294838206464)), (33/73786976294838206464), by norm_num⟩
  | 11 => ⟨((2517356047/147573952589676412928), (14960103029/590295810358705651712)), (23/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-4558150189/1180591620717411303424), (639996495/1180591620717411303424)), (63/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct2 : Sound J_gammaProduct2 F_gammaProduct2 c := by
  apply sound_round (sound_mul (A_gammaProduct1 hcre) (A_gammaInverse2 hcre) S_gammaProduct1 S_gammaInverse2)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct2, J_gammaProduct1, J_gammaInverse2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (3, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((35/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor3 : Sound J_gammaFactor3 F_gammaFactor3 c := by
  apply sound_round (sound_add (A_base hcre) (A_q4 hcre) S_base S_q4)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor3, J_base, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7168000/53010409), (-5955840/53010409)), 0, by norm_num⟩
  | 1 => ⟨((-7954096947200/2810103462347281), (42691461120000/2810103462347281)), 0, by norm_num⟩
  | 2 => ⟨((-11647163085/17592186044416), (-20866775667/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((3919344259/35184372088832), (3025987149/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-11199312135/1125899906842624), (1886097407/562949953421312)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((8724336479/18014398509481984), (-14146716523/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 6 => ⟨((409722103/36028797018963968), (5786200073/72057594037927936)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((-6087175507/1152921504606846976), (-11045378969/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1443586843/2305843009213693952), (125726057/4611686018427387904)), (29/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-3236204461/73786976294838206464), (9836160381/295147905179352825856)), (29/295147905179352825856), by norm_num⟩
  | 10 => ⟨((2581067191/2361183241434822606848), (-22275302425/4722366482869645213696)), (29/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((7218654581/37778931862957161709568), (14368062259/37778931862957161709568)), (29/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-20723053989/604462909807314587353088), (-9054390593/604462909807314587353088)), (115/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (4653/1280)))⁻¹=value ((7168000/53010409), (-5955840/53010409)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/53010409), (-5955840/53010409))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-968610301/549755813888), (10053169335/8796093022208)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((152974031/4398046511104), (-31336459183/35184372088832)), (5/35184372088832), by norm_num⟩
  | 2 => ⟨((1658395081/8796093022208), (9936322561/70368744177664)), (3/70368744177664), by norm_num⟩
  | 3 => ⟨((-6594727353/140737488355328), (71713595/4398046511104)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((5025347069/2251799813685248), (-9944112405/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((9371604417/9007199254740992), (10025003953/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-4209672041/18014398509481984), (3257111789/72057594037927936)), (13/72057594037927936), by norm_num⟩
  | 7 => ⟨((7136933889/576460752303423488), (-4761869049/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 8 => ⟨((3610421017/1152921504606846976), (18078733925/4611686018427387904)), (15/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-12582179287/18446744073709551616), (3734128845/36893488147419103232)), (11/9223372036854775808), by norm_num⟩
  | 10 => ⟨((2441864225/73786976294838206464), (-792842523/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 11 => ⟨((9144236723/1180591620717411303424), (1354897093/147573952589676412928)), (45/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-14172650425/9444732965739290427392), (1518064429/4722366482869645213696)), (63/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct3 : Sound J_gammaProduct3 F_gammaProduct3 c := by
  apply sound_round (sound_mul (A_gammaProduct2 hcre) (A_gammaInverse3 hcre) S_gammaProduct2 S_gammaInverse3)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct3, J_gammaProduct2, J_gammaInverse3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (4, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((43/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor4 : Sound J_gammaFactor4 F_gammaFactor4 c := by
  apply sound_round (sound_add (A_base hcre) (A_q5 hcre) S_base S_q5)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor4, J_base, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8806400/68984809), (-5955840/68984809)), 0, by norm_num⟩
  | 1 => ⟨((-21040325427200/4758903872766481), (52449509376000/4758903872766481)), 0, by norm_num⟩
  | 2 => ⟨((-425652775/2199023255552), (-15733253741/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((14344316383/281474976710656), (6857878937/140737488355328)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-6030621819/1125899906842624), (-4099916763/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 5 => ⟨((13733500093/36028797018963968), (-3118488525/18014398509481984)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-9717647585/576460752303423488), (15855066745/576460752303423488)), (13/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1026631707/9223372036854775808), (-2862989937/1152921504606846976)), (23/9223372036854775808), by norm_num⟩
  | 8 => ⟨((8433915319/73786976294838206464), (11340851721/73786976294838206464)), (21/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-8223070107/590295810358705651712), (-2878374361/590295810358705651712)), (37/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((20771826851/18889465931478580854784), (-1369992857/4722366482869645213696)), (1/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-4357109489/75557863725914323419136), (9971615497/151115727451828646838272)), (7/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((2012217103/2417851639229258349412352), (-16202353033/2417851639229258349412352)), (97/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (4653/1280)))⁻¹=value ((8806400/68984809), (-5955840/68984809)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/68984809), (-5955840/68984809))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2220907737/17592186044416), (5242732151/17592186044416)), (5/70368744177664), by norm_num⟩
  | 1 => ⟨((-5436686937/70368744177664), (-1241748283/8796093022208)), (3/70368744177664), by norm_num⟩
  | 2 => ⟨((26618788747/562949953421312), (4179175677/562949953421312)), (7/562949953421312), by norm_num⟩
  | 3 => ⟨((-8908791731/1125899906842624), (1082891967/140737488355328)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-686205209/2251799813685248), (-19391179455/9007199254740992)), (11/9007199254740992), by norm_num⟩
  | 5 => ⟨((12296550269/36028797018963968), (6359533611/36028797018963968)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((-15948675989/288230376151711744), (8477440355/288230376151711744)), (19/288230376151711744), by norm_num⟩
  | 7 => ⟨((1141327095/1152921504606846976), (-11013718219/1152921504606846976)), (29/2305843009213693952), by norm_num⟩
  | 8 => ⟨((78355841/72057594037927936), (127190023/144115188075855872)), (23/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-428517303/2305843009213693952), (2302780193/36893488147419103232)), (33/73786976294838206464), by norm_num⟩
  | 10 => ⟨((3524464461/590295810358705651712), (-7625687631/295147905179352825856)), (3/36893488147419103232), by norm_num⟩
  | 11 => ⟨((5939890787/2361183241434822606848), (5690915887/2361183241434822606848)), (17/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-2023154173/4722366482869645213696), (1183862355/9444732965739290427392)), (3/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct4 : Sound J_gammaProduct4 F_gammaProduct4 c := by
  apply sound_round (sound_mul (A_gammaProduct3 hcre) (A_gammaInverse4 hcre) S_gammaProduct3 S_gammaInverse4)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct4, J_gammaProduct3, J_gammaInverse4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (5, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((51/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor5 : Sound J_gammaFactor5 F_gammaFactor5 c := by
  apply sound_round (sound_add (A_base hcre) (A_q6 hcre) S_base S_q6)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor5, J_base, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3481600/29412003), (-661760/9804001)), 0, by norm_num⟩
  | 1 => ⟨((-4090100940800/865065920472009), (2303983616000/288355306824003)), 0, by norm_num⟩
  | 2 => ⟨((358115807/35184372088832), (-22253314699/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((2919368981/140737488355328), (21266991059/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-5635606129/2251799813685248), (-3458458553/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((14408775843/72057594037927936), (231936101/36028797018963968)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-3473854547/288230376151711744), (7341339397/1152921504606846976)), (9/1152921504606846976), by norm_num⟩
  | 7 => ⟨((2298631187/4611686018427387904), (-14455568515/18446744073709551616)), (15/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-225303003/73786976294838206464), (9327105459/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-2304921029/1180591620717411303424), (-9075976079/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((289575483/1180591620717411303424), (12211118611/75557863725914323419136)), (55/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-12072131729/604462909807314587353088), (-1556200577/1208925819614629174706176)), (83/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((11852325941/9671406556917033397649408), (-5782000693/9671406556917033397649408)), (63/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (4653/1280)))⁻¹=value ((3481600/29412003), (-661760/9804001)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/29412003), (-661760/9804001))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2911441463/562949953421312), (24656295561/562949953421312)), (1/70368744177664), by norm_num⟩
  | 1 => ⟨((-11517201683/562949953421312), (-3916330213/281474976710656)), (3/281474976710656), by norm_num⟩
  | 2 => ⟨((17516245395/2251799813685248), (-4908590645/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-1810689837/2251799813685248), (4135326631/2251799813685248)), (11/9007199254740992), by norm_num⟩
  | 4 => ⟨((-7053536069/36028797018963968), (-13334372571/36028797018963968)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((22018806807/288230376151711744), (3791679371/288230376151711744)), (23/288230376151711744), by norm_num⟩
  | 6 => ⟨((-686717333/72057594037927936), (5197458789/576460752303423488)), (21/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-2470577891/9223372036854775808), (-4733665859/2305843009213693952)), (17/4611686018427387904), by norm_num⟩
  | 8 => ⟨((10087780715/36893488147419103232), (5295578611/36893488147419103232)), (53/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-11455612005/295147905179352825856), (6099273205/295147905179352825856)), (39/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1328385399/2361183241434822606848), (-28307916033/4722366482869645213696)), (57/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((11890578643/18889465931478580854784), (9242203591/18889465931478580854784)), (81/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-7255263511/75557863725914323419136), (5446433931/151115727451828646838272)), (115/151115727451828646838272), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct5 : Sound J_gammaProduct5 F_gammaProduct5 c := by
  apply sound_round (sound_mul (A_gammaProduct4 hcre) (A_gammaInverse5 hcre) S_gammaProduct4 S_gammaInverse5)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct5, J_gammaProduct4, J_gammaInverse5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (6, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((59/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor6 : Sound J_gammaFactor6 F_gammaFactor6 c := by
  apply sound_round (sound_add (A_base hcre) (A_q7 hcre) S_base S_q7)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor6, J_base, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12083200/110764009), (-5955840/110764009)), 0, by norm_num⟩
  | 1 => ⟨((-55265846067200/12268665689752081), (71965605888000/12268665689752081)), 0, by norm_num⟩
  | 2 => ⟨((3096244887/35184372088832), (-7759164371/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((993321519/140737488355328), (14874998539/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-4933123055/4503599627370496), (-2818123461/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((13459461889/144115188075855872), (1398396737/36028797018963968)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-28304916813/4611686018427387904), (908162989/2305843009213693952)), (17/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2990106867/9223372036854775808), (-6880451061/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-58424535/4611686018427387904), (11149633169/590295810358705651712)), (17/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1730298691/9444732965739290427392), (-1618423245/1180591620717411303424)), (45/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((4059442381/151115727451828646838272), (3010928147/37778931862957161709568)), (59/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-4361759039/1208925819614629174706176), (-4382260979/1208925819614629174706176)), (5/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((2845836035/9671406556917033397649408), (3896398789/38685626227668133590597632)), (105/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (4653/1280)))⁻¹=value ((12083200/110764009), (-5955840/110764009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/110764009), (-5955840/110764009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6573560581/2251799813685248), (316649417/70368744177664)), (11/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3670634251/1125899906842624), (-658330461/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | 2 => ⟨((520682297/562949953421312), (-3205777955/4503599627370496)), (13/18014398509481984), by norm_num⟩
  | 3 => ⟨((-730825869/36028797018963968), (2767627259/9007199254740992)), (9/36028797018963968), by norm_num⟩
  | 4 => ⟨((-6976938123/144115188075855872), (-13590846951/288230376151711744)), (21/288230376151711744), by norm_num⟩
  | 5 => ⟨((29859264177/2305843009213693952), (-1616696137/1152921504606846976)), (41/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-2821094957/2305843009213693952), (17714794445/9223372036854775808)), (19/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-4593616475/36893488147419103232), (-12809454779/36893488147419103232)), (1/1152921504606846976), by norm_num⟩
  | 8 => ⟨((15841291243/295147905179352825856), (1220911157/73786976294838206464)), (51/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-15336678819/2361183241434822606848), (11526892337/2361183241434822606848)), (77/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-358081923/9444732965739290427392), (-10626160407/9444732965739290427392)), (113/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((4809067761/37778931862957161709568), (12070516755/151115727451828646838272)), (161/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-1331923619/75557863725914323419136), (9865411785/1208925819614629174706176)), (229/1208925819614629174706176), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct6 : Sound J_gammaProduct6 F_gammaProduct6 c := by
  apply sound_round (sound_mul (A_gammaProduct5 hcre) (A_gammaInverse6 hcre) S_gammaProduct5 S_gammaInverse6)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct6, J_gammaProduct5, J_gammaInverse6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (7, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((67/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor7 : Sound J_gammaFactor7 F_gammaFactor7 c := by
  apply sound_round (sound_add (A_base hcre) (A_q8 hcre) S_base S_q8)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor7, J_base, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13721600/136568809), (-5955840/136568809)), 0, by norm_num⟩
  | 1 => ⟨((-76405138227200/18651039591678481), (81723654144000/18651039591678481)), 0, by norm_num⟩
  | 2 => ⟨((3879222775/35184372088832), (-2721959227/8796093022208)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((1361021911/1125899906842624), (5052473529/281474976710656)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-8144893115/18014398509481984), (-246401481/281474976710656)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((12048592697/288230376151711744), (4916957685/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-26230902673/9223372036854775808), (-925212181/1152921504606846976)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((5916625953/36893488147419103232), (-3202132497/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-17905752397/2361183241434822606848), (10830718533/2361183241434822606848)), (15/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((10613817123/37778931862957161709568), (-14952672467/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-3314538871/604462909807314587353088), (15721820469/604462909807314587353088)), (21/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-2820900087/9671406556917033397649408), (-6896725443/4835703278458516698824704)), (49/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((7079733655/154742504910672534362390528), (315715183/4835703278458516698824704)), (29/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (4653/1280)))⁻¹=value ((13721600/136568809), (-5955840/136568809)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/136568809), (-5955840/136568809))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4409469319/9007199254740992), (11702455127/36028797018963968)), (7/18014398509481984), by norm_num⟩
  | 1 => ⟨((-6930833197/18014398509481984), (2802569661/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 2 => ⟨((5729939655/72057594037927936), (-17892356511/144115188075855872)), (9/72057594037927936), by norm_num⟩
  | 3 => ⟨((2903772669/288230376151711744), (5725418593/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 4 => ⟨((-19122158343/2305843009213693952), (-10151413843/2305843009213693952)), (31/2305843009213693952), by norm_num⟩
  | 5 => ⟨((4041059731/2305843009213693952), (-3068076153/4611686018427387904)), (31/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-4157901227/36893488147419103232), (11730877973/36893488147419103232)), (59/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-8536644315/295147905179352825856), (-14133386769/295147905179352825856)), (51/295147905179352825856), by norm_num⟩
  | 8 => ⟨((20333215171/2361183241434822606848), (1294823277/1180591620717411303424)), (41/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-16929507149/18889465931478580854784), (2140268003/2361183241434822606848)), (63/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-521647287/18889465931478580854784), (-13333551489/75557863725914323419136)), (47/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((6500552029/302231454903657293676544), (3245088257/302231454903657293676544)), (17/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-13201010145/4835703278458516698824704), (3670965709/2417851639229258349412352)), (97/2417851639229258349412352), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct7 : Sound J_gammaProduct7 F_gammaProduct7 c := by
  apply sound_round (sound_mul (A_gammaProduct6 hcre) (A_gammaInverse7 hcre) S_gammaProduct6 S_gammaInverse7)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct7, J_gammaProduct6, J_gammaInverse7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (8, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((75/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor8 : Sound J_gammaFactor8 F_gammaFactor8 c := by
  apply sound_round (sound_add (A_base hcre) (A_q9 hcre) S_base S_q9)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor8, J_base, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5120000/55216803), (-661760/18405601)), 0, by norm_num⟩
  | 1 => ⟨((-11136531660800/3048895333540809), (3388211200000/1016298444513603)), 0, by norm_num⟩
  | 2 => ⟨((7699252449/70368744177664), (-15497414109/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-626871951/562949953421312), (27421198475/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-6027211587/36028797018963968), (-10531185703/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((2632315675/144115188075855872), (3472625497/144115188075855872)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((-5903011865/4611686018427387904), (-3637721331/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((5425205969/73786976294838206464), (4002261019/295147905179352825856)), (13/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-17248927215/4722366482869645213696), (409126099/590295810358705651712)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5926939917/37778931862957161709568), (-230915919/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-13335655545/2417851639229258349412352), (8890994247/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((4777723951/38685626227668133590597632), (-17026525977/38685626227668133590597632)), (9/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((2706560135/1237940039285380274899124224), (14004567821/618970019642690137449562112)), (75/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (4653/1280)))⁻¹=value ((5120000/55216803), (-661760/18405601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/55216803), (-661760/18405601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8224929775/144115188075855872), (3607662001/288230376151711744)), (15/288230376151711744), by norm_num⟩
  | 1 => ⟨((-20608057355/576460752303423488), (12389009181/576460752303423488)), (15/288230376151711744), by norm_num⟩
  | 2 => ⟨((4819974053/1152921504606846976), (-18458583475/1152921504606846976)), (23/1152921504606846976), by norm_num⟩
  | 3 => ⟨((11328821857/4611686018427387904), (19087842597/4611686018427387904)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((-10289144745/9223372036854775808), (-2377690575/9223372036854775808)), (5/2305843009213693952), by norm_num⟩
  | 5 => ⟨((7191964675/36893488147419103232), (-9799070595/73786976294838206464)), (41/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-1673017065/295147905179352825856), (3187382491/73786976294838206464)), (79/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-11610830669/2361183241434822606848), (-6499094951/1180591620717411303424)), (35/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((11001975969/9444732965739290427392), (-97038285/2361183241434822606848)), (115/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-7841551479/75557863725914323419136), (10511621709/75557863725914323419136)), (45/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-3986330599/604462909807314587353088), (-14317222843/604462909807314587353088)), (135/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((15048654639/4835703278458516698824704), (5811849869/4835703278458516698824704)), (197/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-7049087059/19342813113834066795298816), (9251959213/38685626227668133590597632)), (141/19342813113834066795298816), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct8 : Sound J_gammaProduct8 F_gammaProduct8 c := by
  apply sound_round (sound_mul (A_gammaProduct7 hcre) (A_gammaInverse8 hcre) S_gammaProduct7 S_gammaInverse8)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct8, J_gammaProduct7, J_gammaInverse8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (9, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((83/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor9 : Sound J_gammaFactor9 F_gammaFactor9 c := by
  apply sound_round (sound_add (A_base hcre) (A_q10 hcre) S_base S_q10)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor9, J_base, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16998400/198008809), (-5955840/198008809)), 0, by norm_num⟩
  | 1 => ⟨((-126736786227200/39207488441598481), (101239750656000/39207488441598481)), 0, by norm_num⟩
  | 2 => ⟨((109856925/1099511627776), (-11220208249/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-2128685899/1125899906842624), (18795136741/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-799405211/18014398509481984), (-6966224975/18014398509481984)), (7/72057594037927936), by norm_num⟩
  | 5 => ⟨((278161013/36028797018963968), (2295929149/144115188075855872)), (7/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-10532817963/18446744073709551616), (-10472388095/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((19507246935/590295810358705651712), (4657653923/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-15638595933/9444732965739290427392), (-106468211/590295810358705651712)), (7/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((22300165943/302231454903657293676544), (-5186383189/302231454903657293676544)), (27/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-7033583487/2417851639229258349412352), (8927943659/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((15025265033/154742504910672534362390528), (-19032894905/154742504910672534362390528)), (49/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-1434770393/618970019642690137449562112), (16686806505/2475880078570760549798248448)), (47/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (4653/1280)))⁻¹=value ((16998400/198008809), (-5955840/198008809)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/198008809), (-5955840/198008809))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3041359137/576460752303423488), (-2961342977/4611686018427387904)), (29/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-12171734641/4611686018427387904), (13960376115/4611686018427387904)), (15/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-1012903777/18446744073709551616), (-15401254185/9223372036854775808)), (25/9223372036854775808), by norm_num⟩
  | 3 => ⟨((13386881239/36893488147419103232), (12996804255/36893488147419103232)), (9/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-18357199351/147573952589676412928), (259723397/147573952589676412928)), (45/147573952589676412928), by norm_num⟩
  | 5 => ⟨((10656743041/590295810358705651712), (-11339849409/590295810358705651712)), (3/36893488147419103232), by norm_num⟩
  | 6 => ⟨((1542818973/4722366482869645213696), (5873337085/1180591620717411303424)), (93/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-3194986167/4722366482869645213696), (-5036873261/9444732965739290427392)), (21/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((10262705789/75557863725914323419136), (-1953182763/75557863725914323419136)), (35/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-6145046149/604462909807314587353088), (22022921955/1208925819614629174706176)), (223/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-5397562053/4835703278458516698824704), (-13393989901/4835703278458516698824704)), (169/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((15198462761/38685626227668133590597632), (540023755/4835703278458516698824704)), (249/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-13194692533/309485009821345068724781056), (5045767835/154742504910672534362390528)), (359/309485009821345068724781056), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct9 : Sound J_gammaProduct9 F_gammaProduct9 c := by
  apply sound_round (sound_mul (A_gammaProduct8 hcre) (A_gammaInverse9 hcre) S_gammaProduct8 S_gammaInverse9)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct9, J_gammaProduct8, J_gammaInverse9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (10, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((91/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor10 : Sound J_gammaFactor10 F_gammaFactor10 c := by
  apply sound_round (sound_add (A_base hcre) (A_q11 hcre) S_base S_q11)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor10, J_base, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((18636800/233644009), (-5955840/233644009)), 0, by norm_num⟩
  | 1 => ⟨((-155929142067200/54589522941592081), (110997798912000/54589522941592081)), 0, by norm_num⟩
  | 2 => ⟨((12385673949/140737488355328), (-16536775033/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-1132825469/562949953421312), (6539173213/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((224492913/36028797018963968), (-18539400127/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((6988412311/2305843009213693952), (5961020469/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-582623925/2305843009213693952), (-6895199603/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((8760861153/590295810358705651712), (13797994633/1180591620717411303424)), (15/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-13994879967/18889465931478580854784), (-2615840953/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((1249673983/37778931862957161709568), (121129093/75557863725914323419136)), (3/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-25913624131/19342813113834066795298816), (3459145003/9671406556917033397649408)), (41/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((7562664307/154742504910672534362390528), (-2424818745/77371252455336267181195264)), (9/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-7673910249/4951760157141521099596496896), (9273851661/4951760157141521099596496896)), (31/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (4653/1280)))⁻¹=value ((18636800/233644009), (-5955840/233644009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/233644009), (-5955840/233644009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((116580223/288230376151711744), (-6851474425/36893488147419103232)), (13/18446744073709551616), by norm_num⟩
  | 1 => ⟨((-678500099/4611686018427387904), (11854099089/36893488147419103232)), (27/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-3333143195/73786976294838206464), (-10808583407/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 3 => ⟨((6137864961/147573952589676412928), (7118013583/295147905179352825856)), (9/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-13982506189/1180591620717411303424), (849897907/295147905179352825856)), (45/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((6545160655/4722366482869645213696), (-666542089/295147905179352825856)), (25/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((4774578291/37778931862957161709568), (18747177345/37778931862957161709568)), (97/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-11927013549/151115727451828646838272), (-6569474199/151115727451828646838272)), (89/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((131066477/9444732965739290427392), (-2899264139/604462909807314587353088)), (151/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-4056524493/4835703278458516698824704), (10060206131/4835703278458516698824704)), (243/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-11814480823/77371252455336267181195264), (-22139604717/77371252455336267181195264)), (373/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((27186117069/618970019642690137449562112), (2587062687/309485009821345068724781056)), (555/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-2740689973/618970019642690137449562112), (2422755599/618970019642690137449562112)), (403/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct10 : Sound J_gammaProduct10 F_gammaProduct10 c := by
  apply sound_round (sound_mul (A_gammaProduct9 hcre) (A_gammaInverse10 hcre) S_gammaProduct9 S_gammaInverse10)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct10, J_gammaProduct9, J_gammaInverse10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (11, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((99/8), (4653/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor11 : Sound J_gammaFactor11 F_gammaFactor11 c := by
  apply sound_round (sound_add (A_base hcre) (A_q12 hcre) S_base S_q12)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor11, J_base, J_q12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((204800/2753091), (-60160/2753091)), 0, by norm_num⟩
  | 1 => ⟨((-2129100800/842167783809), (12320768000/7579510054281)), 0, by norm_num⟩
  | 2 => ⟨((10734306783/140737488355328), (-12396591811/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-8442043163/4503599627370496), (1156735429/281474976710656)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((1788544397/72057594037927936), (-12490001879/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((2238093085/2305843009213693952), (7745624727/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-1010002961/9223372036854775808), (-17655583245/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1973744231/295147905179352825856), (9094560909/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-6288263071/18889465931478580854784), (-8064269651/37778931862957161709568)), (5/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((8894203689/604462909807314587353088), (2600592895/604462909807314587353088)), (17/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-22990706333/38685626227668133590597632), (3594315/4835703278458516698824704)), (7/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((13677039473/618970019642690137449562112), (-2018109563/309485009821345068724781056)), (11/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-3716896741/4951760157141521099596496896), (9585899611/19807040628566084398385987584)), (35/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (4653/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (4653/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (4653/1280)))⁻¹=value ((204800/2753091), (-60160/2753091)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((204800/2753091), (-60160/2753091))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1920674541/73786976294838206464), (-13372057155/590295810358705651712)), (41/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-2741419183/590295810358705651712), (1042005561/36893488147419103232)), (11/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-494160561/73786976294838206464), (-6499709489/590295810358705651712)), (21/590295810358705651712), by norm_num⟩
  | 3 => ⟨((2355500041/590295810358705651712), (5768579371/4722366482869645213696)), (63/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((-18509429353/18889465931478580854784), (556267551/1180591620717411303424)), (81/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((1606591905/18889465931478580854784), (-17114843381/75557863725914323419136)), (23/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((5910566837/302231454903657293676544), (3287298415/75557863725914323419136)), (91/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-2425097345/302231454903657293676544), (-3522565643/1208925819614629174706176)), (169/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((6082280957/4835703278458516698824704), (-6183276519/9671406556917033397649408)), (145/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-2195011517/38685626227668133590597632), (4073834825/19342813113834066795298816)), (237/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-11019322615/618970019642690137449562112), (-8171363049/309485009821345068724781056)), (23/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((21790663643/4951760157141521099596496896), (1113189505/2475880078570760549798248448)), (69/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-16338453251/39614081257132168796771975168), (16609589717/39614081257132168796771975168)), (101/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4926418431/274877906944), (10226888709/549755813888)), (317/274877906944), by norm_num⟩
  | 1 => ⟨((-13301071655/549755813888), (162109065/549755813888)), (2705/1099511627776), by norm_num⟩
  | 2 => ⟨((-521872353/68719476736), (-15907003975/2199023255552)), (767/274877906944), by norm_num⟩
  | 3 => ⟨((-1913815829/8796093022208), (-12021923983/4398046511104)), (9595/4398046511104), by norm_num⟩
  | 4 => ⟨((8679239897/35184372088832), (-7139233161/17592186044416)), (22995/17592186044416), by norm_num⟩
  | 5 => ⟨((13684063651/281474976710656), (-2594762477/70368744177664)), (179503/281474976710656), by norm_num⟩
  | 6 => ⟨((2050236969/281474976710656), (-2374562057/562949953421312)), (593465/2251799813685248), by norm_num⟩
  | 7 => ⟨((21950268603/18014398509481984), (-2123759869/9007199254740992)), (427229/4503599627370496), by norm_num⟩
  | 8 => ⟨((17931756315/144115188075855872), (2581905/70368744177664)), (4374811/144115188075855872), by norm_num⟩
  | 9 => ⟨((19867247541/2305843009213693952), (8340301329/2305843009213693952)), (20231877/2305843009213693952), by norm_num⟩
  | 10 => ⟨((11153086819/9223372036854775808), (5675875123/18446744073709551616)), (42791229/18446744073709551616), by norm_num⟩
  | 11 => ⟨((14476109449/147573952589676412928), (16886188315/147573952589676412928)), (20908163/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-918487455/590295810358705651712), (8688981957/1180591620717411303424)), (304665607/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4926418431/274877906944), (10226888709/549755813888)), (635/549755813888), by norm_num⟩
  | 1 => ⟨((-13301071655/549755813888), (162109065/549755813888)), (1353/549755813888), by norm_num⟩
  | 2 => ⟨((-521872353/68719476736), (-15907003975/2199023255552)), (6137/2199023255552), by norm_num⟩
  | 3 => ⟨((-1913815829/8796093022208), (-12021923983/4398046511104)), (19191/8796093022208), by norm_num⟩
  | 4 => ⟨((8679239897/35184372088832), (-7139233161/17592186044416)), (5749/4398046511104), by norm_num⟩
  | 5 => ⟨((13684063651/281474976710656), (-2594762477/70368744177664)), (179515/281474976710656), by norm_num⟩
  | 6 => ⟨((2050236969/281474976710656), (-2374562057/562949953421312)), (148389/562949953421312), by norm_num⟩
  | 7 => ⟨((21950268603/18014398509481984), (-2123759869/9007199254740992)), (1709637/18014398509481984), by norm_num⟩
  | 8 => ⟨((17931756315/144115188075855872), (2581905/70368744177664)), (136893/4503599627370496), by norm_num⟩
  | 9 => ⟨((19867247541/2305843009213693952), (8340301329/2305843009213693952)), (20324111/2305843009213693952), by norm_num⟩
  | 10 => ⟨((11153086819/9223372036854775808), (5675875123/18446744073709551616)), (43529099/18446744073709551616), by norm_num⟩
  | 11 => ⟨((14476109449/147573952589676412928), (16886188315/147573952589676412928)), (89535611/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-918487455/590295810358705651712), (8688981957/1180591620717411303424)), (399112937/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile016Gamma
