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
namespace Reinmann.XiRectangle.Tile019Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨19,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5499/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5499/640))
  have he : value ((3/4), (5499/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/323333401), (-7038720/323333401)), 0, by norm_num⟩
  | 1 => ⟨((-215331142860800/104544488202226801), (154243694592000/104544488202226801)), 0, by norm_num⟩
  | 2 => ⟨((7562994221/140737488355328), (-10191591813/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-4651380587/4503599627370496), (6842924713/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((276996143/144115188075855872), (-32921658649/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 5 => ⟨((1358265933/1152921504606846976), (560823173/144115188075855872)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-12142377261/147573952589676412928), (-8784174711/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 7 => ⟨((19286192621/4722366482869645213696), (7410777539/2361183241434822606848)), (15/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-13038051377/75557863725914323419136), (-4677364455/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1970927225/302231454903657293676544), (1061611397/4835703278458516698824704)), (35/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-8641410465/38685626227668133590597632), (2458158049/38685626227668133590597632)), (13/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((17028825415/2475880078570760549798248448), (-11350914991/2475880078570760549798248448)), (19/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-14512176241/79228162514264337593543950336), (18240023141/79228162514264337593543950336)), (7/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (5499/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (5499/1280)))⁻¹=value ((21913600/323333401), (-7038720/323333401)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/323333401), (-7038720/323333401))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22698746837/8589934592), (667425171/2147483648)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((10956800/323333401), (-3519360/323333401)), 0, by norm_num⟩
  | 2 => ⟨((-53832785715200/104544488202226801), (38560923648000/104544488202226801)), 0, by norm_num⟩
  | 3 => ⟨((10083992295/1125899906842624), (-3397197271/281474976710656)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-4651380587/36028797018963968), (6842924713/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((443193829/2305843009213693952), (-26337326919/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 6 => ⟨((452755311/4611686018427387904), (23928455381/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-1734625323/295147905179352825856), (-20078113625/2361183241434822606848)), (3/590295810358705651712), by norm_num⟩
  | 8 => ⟨((19286192621/75557863725914323419136), (7410777539/37778931862957161709568)), (15/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-5794689501/604462909807314587353088), (-8315314587/2417851639229258349412352)), (23/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((394185445/1208925819614629174706176), (424644559/38685626227668133590597632)), (29/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-25138648625/2475880078570760549798248448), (7151005233/2475880078570760549798248448)), (39/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((11352550277/39614081257132168796771975168), (-7567276661/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (117/20480)), 0, by norm_num⟩
  | 45 => ⟨((101312233673/4080638361600), (-232479/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-2059228178873/83268678451200), (1567020458549/197568495616000)), 0, by norm_num⟩
  | 43 => ⟨((6922361655/274877906944), (-2182914429/274877906944)), (1/549755813888), by norm_num⟩
  | 42 => ⟨((-14188573429/549755813888), (4433658127/549755813888)), (1/549755813888), by norm_num⟩
  | 41 => ⟨((7273014015/274877906944), (-2268556069/274877906944)), (1/549755813888), by norm_num⟩
  | 40 => ⟨((-14912111877/549755813888), (4650063717/549755813888)), (1/549755813888), by norm_num⟩
  | 39 => ⟨((15294251921/549755813888), (-4766890493/549755813888)), (1/274877906944), by norm_num⟩
  | 38 => ⟨((-7848266719/274877906944), (4888664227/549755813888)), (1/274877906944), by norm_num⟩
  | 37 => ⟨((1007552673/34359738368), (-5016657675/549755813888)), (1/274877906944), by norm_num⟩
  | 36 => ⟨((-16568818617/549755813888), (5151586141/549755813888)), (1/274877906944), by norm_num⟩
  | 35 => ⟨((17042399709/549755813888), (-5294006983/549755813888)), (1/274877906944), by norm_num⟩
  | 34 => ⟨((-4385958863/137438953472), (680566525/68719476736)), (1/274877906944), by norm_num⟩
  | 33 => ⟨((9037831897/274877906944), (-5603866179/549755813888)), (1/274877906944), by norm_num⟩
  | 32 => ⟨((-18640736871/549755813888), (360800371/34359738368)), (1/274877906944), by norm_num⟩
  | 31 => ⟨((19242272187/549755813888), (-5952248047/549755813888)), (1/274877906944), by norm_num⟩
  | 30 => ⟨((-1242744725/34359738368), (6143203525/549755813888)), (1/274877906944), by norm_num⟩
  | 29 => ⟨((1285613487/34359738368), (-3173408587/274877906944)), (1/274877906944), by norm_num⟩
  | 28 => ⟨((-10652357007/274877906944), (6564390759/549755813888)), (1/549755813888), by norm_num⟩
  | 27 => ⟨((22094053701/549755813888), (-849676363/68719476736)), (1/549755813888), by norm_num⟩
  | 26 => ⟨((-22944115409/549755813888), (7047583103/549755813888)), (1/274877906944), by norm_num⟩
  | 25 => ⟨((5965546033/137438953472), (-914609191/68719476736)), (1/274877906944), by norm_num⟩
  | 24 => ⟨((-24856758415/549755813888), (1901890205/137438953472)), (1/274877906944), by norm_num⟩
  | 23 => ⟨((25937813963/549755813888), (-7922300727/549755813888)), (1/274877906944), by norm_num⟩
  | 22 => ⟨((-13558569535/274877906944), (2066051873/137438953472)), (1/274877906944), by norm_num⟩
  | 21 => ⟨((14204382887/274877906944), (-1079619659/68719476736)), (1/274877906944), by norm_num⟩
  | 20 => ⟨((-14914765097/274877906944), (4522460435/274877906944)), (1/274877906944), by norm_num⟩
  | 19 => ⟨((15699904783/274877906944), (-4746667985/274877906944)), (1/274877906944), by norm_num⟩
  | 18 => ⟨((-4143063073/68719476736), (2497133321/137438953472)), (1/274877906944), by norm_num⟩
  | 17 => ⟨((17547183929/274877906944), (-2634559357/137438953472)), (1/137438953472), by norm_num⟩
  | 16 => ⟨((-18643914799/274877906944), (5575986489/274877906944)), (1/137438953472), by norm_num⟩
  | 15 => ⟨((2485847003/34359738368), (-5920810649/274877906944)), (1/137438953472), by norm_num⟩
  | 14 => ⟨((-10653519025/137438953472), (1577774721/68719476736)), (1/137438953472), by norm_num⟩
  | 13 => ⟨((22945573281/274877906944), (-6756479223/274877906944)), (1/274877906944), by norm_num⟩
  | 12 => ⟨((-12428423051/137438953472), (7269505745/274877906944)), (1/274877906944), by norm_num⟩
  | 11 => ⟨((13557536029/137438953472), (-3933431055/137438953472)), (1/137438953472), by norm_num⟩
  | 10 => ⟨((-3728007329/34359738368), (4285606395/137438953472)), (1/137438953472), by norm_num⟩
  | 9 => ⟨((4141697303/34359738368), (-2353537273/68719476736)), (1/137438953472), by norm_num⟩
  | 8 => ⟨((-18633980943/137438953472), (652566799/17179869184)), (1/137438953472), by norm_num⟩
  | 7 => ⟨((21289529635/137438953472), (-2929913495/68719476736)), (1/68719476736), by norm_num⟩
  | 6 => ⟨((-24825907819/137438953472), (1669435329/34359738368)), (1/68719476736), by norm_num⟩
  | 5 => ⟨((14883889263/68719476736), (-970183581/17179869184)), (1/34359738368), by norm_num⟩
  | 4 => ⟨((-9289878681/34359738368), (1158273613/17179869184)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((3088840085/8589934592), (-718611347/8589934592)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-18435115061/34359738368), (1894537671/17179869184)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((18183430251/17179869184), (-2785790793/17179869184)), (1/17179869184), by norm_num⟩
  | 0 => ⟨((-8940871499/68719476736), (667425171/2147483648)), (3/68719476736), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (5499/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (5499/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (5499/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((22698746837/8589934592), (667425171/2147483648)), (1/8589934592), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (5499/1280))) (z:=((-21/128), (5499/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((22698746837/8589934592), (667425171/2147483648))) (r:=(1/8589934592)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((17548567569/536870912), (8243021295/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((1937349643/1073741824), (1381599413/8589934592)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((912591244876800/104544488202226801), (-303762121359840/104544488202226801)), 0, by norm_num⟩
  | 3 => ⟨((-3177126579/35184372088832), (2375266669/35184372088832)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((5332707435/4503599627370496), (-15299520263/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 5 => ⟨((-7497608167/576460752303423488), (25189524947/576460752303423488)), (43/576460752303423488), by norm_num⟩
  | 6 => ⟨((-305024035/9223372036854775808), (-20549274871/18446744073709551616)), (63/18446744073709551616), by norm_num⟩
  | 7 => ⟨((5874102451/590295810358705651712), (4045791819/147573952589676412928)), (11/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-9349275371/18889465931478580854784), (-5945875599/9444732965739290427392)), (113/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((11468985915/604462909807314587353088), (7626772137/604462909807314587353088)), (5/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-3106246691/4835703278458516698824704), (-1716143487/9671406556917033397649408)), (217/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((24632202873/1237940039285380274899124224), (-1170086489/1237940039285380274899124224)), (71/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-2804421777/4951760157141521099596496896), (8550975145/39614081257132168796771975168)), (759/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((10367919121/536870912), (11873147051/1073741824)), (5/1073741824), by norm_num⟩
  | 1 => ⟨((1400478731/1073741824), (1381599413/8589934592)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((912591244876800/104544488202226801), (-303762121359840/104544488202226801)), 0, by norm_num⟩
  | 3 => ⟨((-3177126579/35184372088832), (2375266669/35184372088832)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((5332707435/4503599627370496), (-15299520263/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 5 => ⟨((-7497608167/576460752303423488), (25189524947/576460752303423488)), (43/576460752303423488), by norm_num⟩
  | 6 => ⟨((-305024035/9223372036854775808), (-20549274871/18446744073709551616)), (63/18446744073709551616), by norm_num⟩
  | 7 => ⟨((5874102451/590295810358705651712), (4045791819/147573952589676412928)), (11/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-9349275371/18889465931478580854784), (-5945875599/9444732965739290427392)), (113/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((11468985915/604462909807314587353088), (7626772137/604462909807314587353088)), (5/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-3106246691/4835703278458516698824704), (-1716143487/9671406556917033397649408)), (217/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((24632202873/1237940039285380274899124224), (-1170086489/1237940039285380274899124224)), (71/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-2804421777/4951760157141521099596496896), (8550975145/39614081257132168796771975168)), (759/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((21722540979/1073741824), (11873147051/1073741824)), (3/536870912), by norm_num⟩
  | 1 => ⟨((1400478731/1073741824), (1381599413/8589934592)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((912591244876800/104544488202226801), (-303762121359840/104544488202226801)), 0, by norm_num⟩
  | 3 => ⟨((-3177126579/35184372088832), (2375266669/35184372088832)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((5332707435/4503599627370496), (-15299520263/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 5 => ⟨((-7497608167/576460752303423488), (25189524947/576460752303423488)), (43/576460752303423488), by norm_num⟩
  | 6 => ⟨((-305024035/9223372036854775808), (-20549274871/18446744073709551616)), (63/18446744073709551616), by norm_num⟩
  | 7 => ⟨((5874102451/590295810358705651712), (4045791819/147573952589676412928)), (11/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-9349275371/18889465931478580854784), (-5945875599/9444732965739290427392)), (113/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((11468985915/604462909807314587353088), (7626772137/604462909807314587353088)), (5/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-3106246691/4835703278458516698824704), (-1716143487/9671406556917033397649408)), (217/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((24632202873/1237940039285380274899124224), (-1170086489/1237940039285380274899124224)), (71/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-2804421777/4951760157141521099596496896), (8550975145/39614081257132168796771975168)), (759/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((430662285721600/104544488202226801), (-308487389184000/104544488202226801)), 0, by norm_num⟩
  | 1 => ⟨((-7562994221/35184372088832), (10191591813/35184372088832)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((218033465/35184372088832), (-20528774139/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 3 => ⟨((-276996143/18014398509481984), (32921658649/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((-3395664833/288230376151711744), (-2804115865/72057594037927936)), (7/576460752303423488), by norm_num⟩
  | 5 => ⟨((4553391473/4611686018427387904), (13176262067/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-1054713659/18446744073709551616), (-12968860693/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 7 => ⟨((13038051377/4722366482869645213696), (4677364455/4722366482869645213696)), (5/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-8869172513/75557863725914323419136), (-597156411/151115727451828646838272)), (15/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((21603526163/4835703278458516698824704), (-3072697561/2417851639229258349412352)), (23/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-5853658737/38685626227668133590597632), (975469257/9671406556917033397649408)), (9/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((5442066091/1237940039285380274899124224), (-13680017355/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-3812100633/39614081257132168796771975168), (315274047/1237940039285380274899124224)), (21/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7562994221/35184372088832), (-10191591813/35184372088832)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-218033465/17592186044416), (20528774139/562949953421312)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((207747107/4503599627370496), (-24691243987/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((3395664833/72057594037927936), (2804115865/18014398509481984)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((-11383478683/2305843009213693952), (-16470327583/2305843009213693952)), (7/2305843009213693952), by norm_num⟩
  | 5 => ⟨((3164140977/9223372036854775808), (607915345/2305843009213693952)), (7/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-22816589911/1180591620717411303424), (-8185387797/1180591620717411303424)), (7/590295810358705651712), by norm_num⟩
  | 7 => ⟨((8869172513/9444732965739290427392), (597156411/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-12151983467/302231454903657293676544), (864196189/75557863725914323419136)), (23/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((7317073421/4835703278458516698824704), (-4877346285/4835703278458516698824704)), (19/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-7482840875/154742504910672534362390528), (2351252983/38685626227668133590597632)), (31/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((2859075475/2475880078570760549798248448), (-945822141/309485009821345068724781056)), (25/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-271155943/39614081257132168796771975168), (10734399683/79228162514264337593543950336)), (19/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4651380587/562949953421312), (-6842924713/281474976710656)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((-553992285/9007199254740992), (32921658649/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 2 => ⟨((-3395664833/36028797018963968), (-2804115865/9007199254740992)), (3/36028797018963968), by norm_num⟩
  | 3 => ⟨((1897246447/144115188075855872), (10980218389/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 4 => ⟨((-5273568295/4611686018427387904), (-8105537933/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((22816589911/295147905179352825856), (8185387797/295147905179352825856)), (13/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-2586841983/590295810358705651712), (-696682479/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((16202644623/75557863725914323419136), (-2304523171/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-2743902533/302231454903657293676544), (1829004857/302231454903657293676544)), (13/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((12471401459/38685626227668133590597632), (-15675019887/38685626227668133590597632)), (23/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-2620819185/309485009821345068724781056), (3468014517/154742504910672534362390528)), (21/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((271155943/4951760157141521099596496896), (-10734399683/9903520314283042199192993792)), (17/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((984624969/79228162514264337593543950336), (14786379735/316912650057057350374175801344)), (7/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((276996143/9007199254740992), (-32921658649/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 1 => ⟨((3395664833/36028797018963968), (2804115865/9007199254740992)), (3/36028797018963968), by norm_num⟩
  | 2 => ⟨((-11383478683/576460752303423488), (-16470327583/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 3 => ⟨((5273568295/2305843009213693952), (8105537933/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-7130184347/36893488147419103232), (-5115867373/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 5 => ⟨((31042103795/2361183241434822606848), (1045023719/2361183241434822606848)), (21/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-14177314045/18889465931478580854784), (4032915549/18889465931478580854784)), (3/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((2743902533/75557863725914323419136), (-1829004857/75557863725914323419136)), (13/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-14030326641/9671406556917033397649408), (17634397373/9671406556917033397649408)), (25/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((6552047963/154742504910672534362390528), (-8670036293/77371252455336267181195264)), (3/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-745678843/2475880078570760549798248448), (29519599129/4951760157141521099596496896)), (11/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-5907749815/79228162514264337593543950336), (-22179569603/79228162514264337593543950336)), (5/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((4710528441/633825300114114700748351602688), (14662305209/1267650600228229401496703205376)), (35/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1358265933/36028797018963968), (-560823173/4503599627370496)), (3/72057594037927936), by norm_num⟩
  | 1 => ⟨((4553391473/288230376151711744), (6588131033/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 2 => ⟨((-3164140977/1152921504606846976), (-607915345/288230376151711744)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((22816589911/73786976294838206464), (2046346949/18446744073709551616)), (15/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-31042103795/1180591620717411303424), (-1045023719/1180591620717411303424)), (23/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((8506388427/4722366482869645213696), (-4839498659/9444732965739290427392)), (1/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-1920731773/18889465931478580854784), (10242427199/151115727451828646838272)), (19/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((11224261313/2417851639229258349412352), (-7053758949/1208925819614629174706176)), (21/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-5896843167/38685626227668133590597632), (15606065327/38685626227668133590597632)), (11/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((745678843/618970019642690137449562112), (-29519599129/1237940039285380274899124224)), (11/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((1624631199/4951760157141521099596496896), (6099381641/4951760157141521099596496896)), (11/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-5652634129/158456325028528675187087900672), (-4398691563/79228162514264337593543950336)), (41/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((13024582663/5070602400912917605986812821504), (670338891/316912650057057350374175801344)), (37/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-12142377261/2305843009213693952), (-8784174711/1152921504606846976)), (5/1152921504606846976), by norm_num⟩
  | 1 => ⟨((1054713659/576460752303423488), (12968860693/9223372036854775808)), (11/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-22816589911/73786976294838206464), (-8185387797/73786976294838206464)), (1/4611686018427387904), by norm_num⟩
  | 3 => ⟨((2586841983/73786976294838206464), (696682479/590295810358705651712)), (17/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-14177314045/4722366482869645213696), (4032915549/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((1920731773/9444732965739290427392), (-10242427199/75557863725914323419136)), (21/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-13094971531/1208925819614629174706176), (16458770881/1208925819614629174706176)), (27/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((1965614389/4835703278458516698824704), (-20808087103/19342813113834066795298816)), (1/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-1118518265/309485009821345068724781056), (22139699347/309485009821345068724781056)), (9/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-2707718665/2475880078570760549798248448), (-2541409017/618970019642690137449562112)), (19/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((5181581285/39614081257132168796771975168), (16128535731/79228162514264337593543950336)), (39/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-13024582663/1267650600228229401496703205376), (-10725422257/1267650600228229401496703205376)), (39/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((13394548327/20282409603651670423947251286016), (5320436017/20282409603651670423947251286016)), (37/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19286192621/36893488147419103232), (-7410777539/18446744073709551616)), (15/36893488147419103232), by norm_num⟩
  | 1 => ⟨((6519025689/36893488147419103232), (4677364455/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-8869172513/295147905179352825856), (-597156411/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 3 => ⟨((16202644623/4722366482869645213696), (-2304523171/2361183241434822606848)), (17/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((-2743902533/9444732965739290427392), (1829004857/9444732965739290427392)), (1/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((11224261313/604462909807314587353088), (-7053758949/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-7862457555/9671406556917033397649408), (20808087103/9671406556917033397649408)), (9/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((319576647/38685626227668133590597632), (-25302513539/154742504910672534362390528)), (45/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((6962705139/2475880078570760549798248448), (26140207033/2475880078570760549798248448)), (27/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-7402258979/19807040628566084398385987584), (-11520382665/19807040628566084398385987584)), (31/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((1279200083/39614081257132168796771975168), (8427117487/316912650057057350374175801344)), (33/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-11481041423/5070602400912917605986812821504), (-4560373729/5070602400912917605986812821504)), (67/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((22227264293/162259276829213363391578010288128), (749123611/81129638414606681695789005144064)), (67/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-13038051377/295147905179352825856), (-4677364455/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 1 => ⟨((8869172513/590295810358705651712), (298578205/590295810358705651712)), (17/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((-12151983467/4722366482869645213696), (864196189/1180591620717411303424)), (7/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((2743902533/9444732965739290427392), (-1829004857/9444732965739290427392)), (17/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((-14030326641/604462909807314587353088), (17634397373/604462909807314587353088)), (17/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((5896843167/4835703278458516698824704), (-15606065327/4835703278458516698824704)), (15/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((-139814783/9671406556917033397649408), (22139699347/77371252455336267181195264)), (11/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((-6962705139/1237940039285380274899124224), (-3267525879/154742504910672534362390528)), (15/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((8327541351/9903520314283042199192993792), (6480215249/4951760157141521099596496896)), (19/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-6396000415/79228162514264337593543950336), (-10533896859/158456325028528675187087900672)), (45/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((15786431957/2535301200456458802993406410752), (6270513877/2535301200456458802993406410752)), (51/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-16670448219/40564819207303340847894502572032), (-140460677/5070602400912917605986812821504)), (55/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((7695232227/324518553658426726783156020576256), (-1911641343/324518553658426726783156020576256)), (57/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1970927225/590295810358705651712), (-1061611397/9444732965739290427392)), (35/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((21603526163/18889465931478580854784), (-6145395123/18889465931478580854784)), (7/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((-7317073421/37778931862957161709568), (4877346285/37778931862957161709568)), (25/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((12471401459/604462909807314587353088), (-15675019887/604462909807314587353088)), (33/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((-6552047963/4835703278458516698824704), (8670036293/2417851639229258349412352)), (35/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((745678843/38685626227668133590597632), (-29519599129/77371252455336267181195264)), (65/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((5415437331/618970019642690137449562112), (2541409017/77371252455336267181195264)), (53/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((-7402258979/4951760157141521099596496896), (-11520382665/4951760157141521099596496896)), (19/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((6396000415/39614081257132168796771975168), (10533896859/79228162514264337593543950336)), (51/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((-1096279997/79228162514264337593543950336), (-6967237641/1267650600228229401496703205376)), (63/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((5093748067/5070602400912917605986812821504), (686696643/10141204801825835211973625643008)), (75/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-2565077409/40564819207303340847894502572032), (5097710249/324518553658426726783156020576256)), (85/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((17917078797/5192296858534827628530496329220096), (-11090945325/5192296858534827628530496329220096)), (23/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8641410465/37778931862957161709568), (2458158049/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((11707317473/151115727451828646838272), (-7803754057/151115727451828646838272)), (23/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-7482840875/604462909807314587353088), (2351252983/151115727451828646838272)), (11/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((2620819185/2417851639229258349412352), (-13872058069/4835703278458516698824704)), (1/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-745678843/38685626227668133590597632), (14759799565/38685626227668133590597632)), (35/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-6498524797/618970019642690137449562112), (-6099381641/154742504910672534362390528)), (69/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((10363162571/4951760157141521099596496896), (8064267865/2475880078570760549798248448)), (15/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-1279200083/4951760157141521099596496896), (-8427117487/39614081257132168796771975168)), (23/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((15786431957/633825300114114700748351602688), (6270513877/633825300114114700748351602688)), (65/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((-5093748067/2535301200456458802993406410752), (-686696643/5070602400912917605986812821504)), (85/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((22572681199/162259276829213363391578010288128), (-2803740637/81129638414606681695789005144064)), (105/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((-5375123639/649037107316853453566312041152512), (6654567195/1298074214633706907132624082305024)), (63/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((4280631721/10384593717069655257060992658440192), (-10047125923/20769187434139310514121985316880384)), (71/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/970000203), (-586560/323333401)), 0, by norm_num⟩
  | 1 => ⟨((-53832785715200/313633464606680403), (12853641216000/104544488202226801)), 0, by norm_num⟩
  | 2 => ⟨((10083992295/2251799813685248), (-3397197271/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-6201840783/72057594037927936), (18247799235/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((369328191/2305843009213693952), (-21947772433/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 5 => ⟨((452755311/4611686018427387904), (23928455381/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-4047459087/590295810358705651712), (-2928058237/295147905179352825856)), (7/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((12857461747/37778931862957161709568), (9881036719/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-17384068503/1208925819614629174706176), (-1559121485/302231454903657293676544)), (17/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((21023223733/38685626227668133590597632), (707740931/38685626227668133590597632)), (3/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-2880470155/154742504910672534362390528), (6555088131/1237940039285380274899124224)), (35/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((11352550277/19807040628566084398385987584), (-7567276661/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-9674784161/633825300114114700748351602688), (12160015427/633825300114114700748351602688)), (19/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10864302647/536870912), (11871199173/1073741824)), (7/1073741824), by norm_num⟩
  | 1 => ⟨((22404710903/17179869184), (1382655537/8589934592)), (3/17179869184), by norm_num⟩
  | 2 => ⟨((9602796485/1099511627776), (-3201351489/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-6360309643/70368744177664), (9536706909/140737488355328)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((5333428779/4503599627370496), (-15385253749/9007199254740992)), (9/4503599627370496), by norm_num⟩
  | 5 => ⟨((-7441013753/576460752303423488), (25376466005/576460752303423488)), (11/144115188075855872), by norm_num⟩
  | 6 => ⟨((-368265583/9223372036854775808), (-20732278511/18446744073709551616)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((6075000291/590295810358705651712), (16337558475/590295810358705651712)), (89/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-9620901441/18889465931478580854784), (-11989196291/18889465931478580854784)), (57/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5898736893/302231454903657293676544), (7637830589/604462909807314587353088)), (161/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-25570091067/38685626227668133590597632), (-1664931861/9671406556917033397649408)), (109/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((25341737265/1237940039285380274899124224), (-3209065/2417851639229258349412352)), (571/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-11520024113/19807040628566084398385987584), (9310976109/39614081257132168796771975168)), (381/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-672266153/1125899906842624), (3623677089/4503599627370496)), (3/18014398509481984), by norm_num⟩
  | 1 => ⟨((2480736313/72057594037927936), (-3649559847/36028797018963968)), (3/144115188075855872), by norm_num⟩
  | 2 => ⟨((-36932819/288230376151711744), (8779108973/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((-4829389985/36893488147419103232), (-3988075897/9223372036854775808)), (5/36893488147419103232), by norm_num⟩
  | 4 => ⟨((8094918175/590295810358705651712), (2928058237/147573952589676412928)), (3/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-18000446447/18889465931478580854784), (-6916725703/9444732965739290427392)), (11/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((16225130603/302231454903657293676544), (5820720211/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-25227868481/9671406556917033397649408), (-424644559/4835703278458516698824704)), (5/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((17282820931/154742504910672534362390528), (-4916316097/154742504910672534362390528)), (17/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-10406504421/2475880078570760549798248448), (108385473/38685626227668133590597632)), (7/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((5321131289/39614081257132168796771975168), (-6688008485/39614081257132168796771975168)), (23/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-8132481351/2535301200456458802993406410752), (21522708275/2535301200456458802993406410752)), (9/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((1542576031/81129638414606681695789005144064), (-30533403543/81129638414606681695789005144064)), (55/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21728604653/1073741824), (11871200037/1073741824)), (1/134217728), by norm_num⟩
  | 1 => ⟨((11202355747/8589934592), (1382654667/8589934592)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((1200349543/137438953472), (-6402686233/2199023255552)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-12720637709/140737488355328), (1192080757/17592186044416)), (7/140737488355328), by norm_num⟩
  | 4 => ⟨((10666981077/9007199254740992), (-15385075035/9007199254740992)), (19/9007199254740992), by norm_num⟩
  | 5 => ⟨((-7441563083/576460752303423488), (12688021921/288230376151711744)), (45/576460752303423488), by norm_num⟩
  | 6 => ⟨((-735540863/18446744073709551616), (-10365961621/9223372036854775808)), (65/18446744073709551616), by norm_num⟩
  | 7 => ⟨((759182563/73786976294838206464), (16337506639/590295810358705651712)), (45/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-4809395861/9444732965739290427392), (-11989796427/18889465931478580854784)), (115/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((737183321/37778931862957161709568), (477470257/37778931862957161709568)), (81/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-12782447325/19342813113834066795298816), (-3333129351/19342813113834066795298816)), (437/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((25337766327/1237940039285380274899124224), (-1632532145/1237940039285380274899124224)), (143/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-23039295015/39614081257132168796771975168), (9296067221/39614081257132168796771975168)), (763/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((450228651/18446744073709551616), (-26755379727/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 1 => ⟨((689912855/9223372036854775808), (4557801025/18446744073709551616)), (3/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-9251335057/590295810358705651712), (-13385409083/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 3 => ⟨((8571641165/4722366482869645213696), (1646839453/1180591620717411303424)), (13/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-5794689501/37778931862957161709568), (-8315314587/151115727451828646838272)), (1/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((25227868481/2417851639229258349412352), (424644559/1208925819614629174706176)), (9/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-23043761241/38685626227668133590597632), (3277544065/19342813113834066795298816)), (21/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((17839721865/618970019642690137449562112), (-11891434753/618970019642690137449562112)), (11/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-11402424191/9903520314283042199192993792), (7165723377/4951760157141521099596496896)), (21/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((5324838979/158456325028528675187087900672), (-14092249467/158456325028528675187087900672)), (21/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-151503003/633825300114114700748351602688), (5997632839/1267650600228229401496703205376)), (37/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-4801218897/81129638414606681695789005144064), (-18025301011/81129638414606681695789005144064)), (17/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((3828238987/649037107316853453566312041152512), (5958016085/649037107316853453566312041152512)), (29/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21728604653/1073741824), (11871200035/1073741824)), (9/1073741824), by norm_num⟩
  | 1 => ⟨((22404711495/17179869184), (1382654669/8589934592)), (5/17179869184), by norm_num⟩
  | 2 => ⟨((9602796327/1099511627776), (-6402686283/2199023255552)), (3/2199023255552), by norm_num⟩
  | 3 => ⟨((-6360318727/70368744177664), (2384161563/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((10666979695/9007199254740992), (-15385075531/9007199254740992)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1860389267/144115188075855872), (6344011011/144115188075855872)), (23/288230376151711744), by norm_num⟩
  | 6 => ⟨((-735551851/18446744073709551616), (-5182980029/4611686018427387904)), (33/9223372036854775808), by norm_num⟩
  | 7 => ⟨((6073477517/590295810358705651712), (8168747649/295147905179352825856)), (91/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-4809406735/9444732965739290427392), (-2997442273/4722366482869645213696)), (29/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((11794953449/604462909807314587353088), (3819735177/302231454903657293676544)), (163/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-25564903897/38685626227668133590597632), (-6666075669/38685626227668133590597632)), (219/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((12668846533/618970019642690137449562112), (-1632807189/1237940039285380274899124224)), (573/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-11519530679/19807040628566084398385987584), (9296430869/39614081257132168796771975168)), (191/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7401068045/2361183241434822606848), (10708327267/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((-5142984699/4722366482869645213696), (-7904829375/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((13907254803/75557863725914323419136), (311824297/4722366482869645213696)), (11/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-12613934241/604462909807314587353088), (-849289117/1208925819614629174706176)), (11/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((17282820931/9671406556917033397649408), (-2458158049/4835703278458516698824704)), (9/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((-9365853979/77371252455336267181195264), (6243003245/77371252455336267181195264)), (27/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((7981696933/1237940039285380274899124224), (-10032012727/1237940039285380274899124224)), (9/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((-2396177541/9903520314283042199192993792), (1585378065/2475880078570760549798248448)), (5/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((340881757/158456325028528675187087900672), (-26989347775/633825300114114700748351602688)), (45/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((6601675983/10141204801825835211973625643008), (12392394445/5070602400912917605986812821504)), (47/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((-12633188657/162259276829213363391578010288128), (-9830726541/81129638414606681695789005144064)), (49/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((3969396621/649037107316853453566312041152512), (6537400233/1298074214633706907132624082305024)), (49/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((-8164296123/20769187434139310514121985316880384), (-6485864859/41538374868278621028243970633760768)), (23/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21728604653/1073741824), (11871200035/1073741824)), (5/536870912), by norm_num⟩
  | 1 => ⟨((22404711495/17179869184), (1382654669/8589934592)), (3/8589934592), by norm_num⟩
  | 2 => ⟨((9602796327/1099511627776), (-6402686283/2199023255552)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-12720637457/140737488355328), (2384161563/35184372088832)), (9/140737488355328), by norm_num⟩
  | 4 => ⟨((10666979711/9007199254740992), (-961567221/562949953421312)), (21/9007199254740992), by norm_num⟩
  | 5 => ⟨((-3720778569/288230376151711744), (25376044091/576460752303423488)), (47/576460752303423488), by norm_num⟩
  | 6 => ⟨((-183887933/4611686018427387904), (-20731920265/18446744073709551616)), (67/18446744073709551616), by norm_num⟩
  | 7 => ⟨((3036738687/295147905179352825856), (4084373919/147573952589676412928)), (23/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-9618813429/18889465931478580854784), (-1498721237/2361183241434822606848)), (117/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((5897476921/302231454903657293676544), (7639471831/604462909807314587353088)), (41/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-25564906909/38685626227668133590597632), (-6666080357/38685626227668133590597632)), (439/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((25337700637/1237940039285380274899124224), (-816400477/618970019642690137449562112)), (287/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-11519538465/19807040628566084398385987584), (2324106171/9903520314283042199192993792)), (765/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-22476371397/604462909807314587353088), (-8063335357/604462909807314587353088)), (11/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((30579234523/2417851639229258349412352), (1029441353/2417851639229258349412352)), (15/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((-163663077/75557863725914323419136), (5959171027/9671406556917033397649408)), (25/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((9460458565/38685626227668133590597632), (-1576515971/9671406556917033397649408)), (15/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((-6046740101/309485009821345068724781056), (3800004821/154742504910672534362390528)), (31/618970019642690137449562112), by norm_num⟩
  | 5 => ⟨((1270700211/1237940039285380274899124224), (-105091349/38685626227668133590597632)), (27/4951760157141521099596496896), by norm_num⟩
  | 6 => ⟨((-964110019/79228162514264337593543950336), (19083377215/79228162514264337593543950336)), (39/79228162514264337593543950336), by norm_num⟩
  | 7 => ⟨((-6001523621/1267650600228229401496703205376), (-22531626263/1267650600228229401496703205376)), (53/1267650600228229401496703205376), by norm_num⟩
  | 8 => ⟨((7177948101/10141204801825835211973625643008), (349102505/316912650057057350374175801344)), (17/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-5513050863/81129638414606681695789005144064), (-9079722545/162259276829213363391578010288128)), (5/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((13607160205/2596148429267413814265248164610048), (2702443691/1298074214633706907132624082305024)), (45/2596148429267413814265248164610048), by norm_num⟩
  | 11 => ⟨((-28738281105/83076749736557242056487941267521536), (-1937127721/83076749736557242056487941267521536)), (3/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((13265854883/664613997892457936451903530140172288), (-6590978907/1329227995784915872903807060280344576)), (99/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21728604653/1073741824), (11871200035/1073741824)), (11/1073741824), by norm_num⟩
  | 1 => ⟨((22404711495/17179869184), (1382654669/8589934592)), (7/17179869184), by norm_num⟩
  | 2 => ⟨((9602796327/1099511627776), (-6402686283/2199023255552)), (5/2199023255552), by norm_num⟩
  | 3 => ⟨((-12720637457/140737488355328), (2384161563/35184372088832)), (5/70368744177664), by norm_num⟩
  | 4 => ⟨((10666979711/9007199254740992), (-961567221/562949953421312)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((-7441557137/576460752303423488), (25376044089/576460752303423488)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-183887933/4611686018427387904), (-20731920261/18446744073709551616)), (17/4611686018427387904), by norm_num⟩
  | 7 => ⟨((6073477371/590295810358705651712), (8168747833/295147905179352825856)), (93/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-1202351677/2361183241434822606848), (-11989769875/18889465931478580854784)), (59/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((11794953801/604462909807314587353088), (7639471797/604462909807314587353088)), (165/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-12782453353/19342813113834066795298816), (-1666520069/9671406556917033397649408)), (55/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((25337700209/1237940039285380274899124224), (-1632800983/1237940039285380274899124224)), (575/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-23039076139/39614081257132168796771975168), (1162053061/4951760157141521099596496896)), (383/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1060488779/2417851639229258349412352), (-603338781/4835703278458516698824704)), (13/19342813113834066795298816), by norm_num⟩
  | 1 => ⟨((-5746968675/38685626227668133590597632), (7661521133/77371252455336267181195264)), (3/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((14692913969/618970019642690137449562112), (-2308398533/77371252455336267181195264)), (11/154742504910672534362390528), by norm_num⟩
  | 3 => ⟨((-5146103125/2475880078570760549798248448), (13619222911/2475880078570760549798248448)), (33/2475880078570760549798248448), by norm_num⟩
  | 4 => ⟨((1464175875/39614081257132168796771975168), (-14490784237/19807040628566084398385987584)), (35/19807040628566084398385987584), by norm_num⟩
  | 5 => ⟨((3190040633/158456325028528675187087900672), (23952851921/316912650057057350374175801344)), (69/316912650057057350374175801344), by norm_num⟩
  | 6 => ⟨((-2543570327/633825300114114700748351602688), (-7917286759/1267650600228229401496703205376)), (15/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((10047080825/20282409603651670423947251286016), (8273523005/20282409603651670423947251286016)), (23/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((-15498705003/324518553658426726783156020576256), (-6156226123/324518553658426726783156020576256)), (65/324518553658426726783156020576256), by norm_num⟩
  | 9 => ⟨((20003633213/5192296858534827628530496329220096), (84272595/324518553658426726783156020576256)), (85/5192296858534827628530496329220096), by norm_num⟩
  | 10 => ⟨((-11080633293/41538374868278621028243970633760768), (5505278097/83076749736557242056487941267521536)), (13/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((10554310925/664613997892457936451903530140172288), (-6533279601/664613997892457936451903530140172288)), (125/1329227995784915872903807060280344576), by norm_num⟩
  | 12 => ⟨((-4202611993/5316911983139663491615228241121378304), (9864004813/10633823966279326983230456482242756608)), (71/10633823966279326983230456482242756608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21728604653/1073741824), (11871200035/1073741824)), (3/268435456), by norm_num⟩
  | 1 => ⟨((22404711495/17179869184), (1382654669/8589934592)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((9602796327/1099511627776), (-6402686283/2199023255552)), (3/1099511627776), by norm_num⟩
  | 3 => ⟨((-12720637457/140737488355328), (2384161563/35184372088832)), (11/140737488355328), by norm_num⟩
  | 4 => ⟨((10666979711/9007199254740992), (-961567221/562949953421312)), (23/9007199254740992), by norm_num⟩
  | 5 => ⟨((-7441557137/576460752303423488), (25376044089/576460752303423488)), (49/576460752303423488), by norm_num⟩
  | 6 => ⟨((-183887933/4611686018427387904), (-20731920261/18446744073709551616)), (69/18446744073709551616), by norm_num⟩
  | 7 => ⟨((6073477371/590295810358705651712), (8168747833/295147905179352825856)), (47/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-9618813417/18889465931478580854784), (-11989769875/18889465931478580854784)), (119/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((11794953803/604462909807314587353088), (7639471797/604462909807314587353088)), (83/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-6391226679/9671406556917033397649408), (-6666080273/38685626227668133590597632)), (441/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((25337700229/1237940039285380274899124224), (-1632800995/1237940039285380274899124224)), (9/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-11519538085/19807040628566084398385987584), (9296424525/39614081257132168796771975168)), (767/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19429380050201/524288), (-321595209339945/524288)), (18464611/1048576), by norm_num⟩
  | 1 => ⟨((2352997601/16), (-3175912705/4)), (209/8), by norm_num⟩
  | 2 => ⟨((5066618737/32), (-8181649425/16)), (627/32), by norm_num⟩
  | 3 => ⟨((6119532607/64), (-13993271055/64)), (317/32), by norm_num⟩
  | 4 => ⟨((10226976303/256), (-17879139305/256)), (969/256), by norm_num⟩
  | 5 => ⟨((6532479873/512), (-18198566287/1024)), (1197/1024), by norm_num⟩
  | 6 => ⟨((13521367305/4096), (-7680189091/2048)), (311/1024), by norm_num⟩
  | 7 => ⟨((11774210629/16384), (-11044053607/16384)), (559/8192), by norm_num⟩
  | 8 => ⟨((4429524389/32768), (-13783689609/131072)), (111/8192), by norm_num⟩
  | 9 => ⟨((11747645323/524288), (-1890563573/131072)), (633/262144), by norm_num⟩
  | 10 => ⟨((13936299135/4194304), (-3677496965/2097152)), (205/524288), by norm_num⟩
  | 11 => ⟨((14967911521/33554432), (-6362203227/33554432)), (975/16777216), by norm_num⟩
  | 12 => ⟨((14695663993/268435456), (-2440798443/134217728)), (2147/268435456), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1610335859391259/10141204801825835211973625643008), (-983767511169/5070602400912917605986812821504)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1813793374848133/633825300114114700748351602688), (-2414212893185/633825300114114700748351602688)), (17907/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((482296687464299/9903520314283042199192993792), (-2723150735221/39614081257132168796771975168)), (20203/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((482866675974377/618970019642690137449562112), (-1449733648859/1237940039285380274899124224)), (21515/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((453294343314119/38685626227668133590597632), (-1453157363551/77371252455336267181195264)), (21569/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((794481617510333/4835703278458516698824704), (-2731967041813/9671406556917033397649408)), (2535/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1293319670010977/604462909807314587353088), (-1198896944433/302231454903657293676544)), (17803/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1943994015750629/75557863725914323419136), (-977550041629/18889465931478580854784)), (1815/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((334942286842659/1180591620717411303424), (-736191831857/1180591620717411303424)), (21877/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((839820746407049/295147905179352825856), (-4068849660547/590295810358705651712)), (30239/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1896408451803873/73786976294838206464), (-5115937292439/73786976294838206464)), (38037/73786976294838206464), by norm_num⟩
  | 7 => ⟨((952486441049657/4611686018427387904), (-2898403947977/4611686018427387904)), (43123/9223372036854775808), by norm_num⟩
  | 6 => ⟨((209569388510675/144115188075855872), (-5848984668095/1152921504606846976)), (43541/1152921504606846976), by norm_num⟩
  | 5 => ⟨((316801744992409/36028797018963968), (-2588595184349/72057594037927936)), (19287/72057594037927936), by norm_num⟩
  | 4 => ⟨((1601339764168055/36028797018963968), (-7886036247985/36028797018963968)), (58825/36028797018963968), by norm_num⟩
  | 3 => ⟨((406934094409625/2251799813685248), (-5035809799925/4503599627370496)), (37625/4503599627370496), by norm_num⟩
  | 2 => ⟨((627255059077103/1125899906842624), (-2600032906963/562949953421312)), (77893/2251799813685248), by norm_num⟩
  | 1 => ⟨((1324110722460257/1125899906842624), (-2055996551371/140737488355328)), (30919/281474976710656), by norm_num⟩
  | 0 => ⟨((1544186014787265/1125899906842624), (-4556357704433/140737488355328)), (138059/562949953421312), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1544186014787265/1125899906842624), (-4556357704433/140737488355328)), (526653291942405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1058345314919599/562949953421312), (-99985638905105/1125899906842624)), (775279/1125899906842624), by norm_num⟩
  | 2 => ⟨((31019507063397/8796093022208), (-23496611877163/70368744177664)), (1526373/562949953421312), by norm_num⟩
  | 3 => ⟨((1734558100323701/140737488355328), (-331444115586035/140737488355328)), (2946219/140737488355328), by norm_num⟩
  | 4 => ⟨((643671027953809/4398046511104), (-127655458535965/2199023255552)), (2703125/4398046511104), by norm_num⟩
  | 5 => ⟨((310088601774619/17179869184), (-583839609332127/34359738368)), (8633311/34359738368), by norm_num⟩
  | 6 => ⟨((19429380050201/524288), (-321595209339945/524288)), (18464611/1048576), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((21728604653/1073741824), (11871200035/1073741824)), (3/268435456), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/33336601), (-7038720/33336601)), 0, by norm_num⟩
  | 1 => ⟨((22234235699200/1111328966233201), (15856828416000/1111328966233201)), 0, by norm_num⟩
  | 2 => ⟨((-19195911433/8796093022208), (896117139/549755813888)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-3460204763/35184372088832), (-20087831843/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((1177256511/35184372088832), (-414794221/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-1185314457/1125899906842624), (500637841/140737488355328)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-382770281/1125899906842624), (-8334763103/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 7 => ⟨((10350163797/288230376151711744), (-8091797519/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 8 => ⟨((2018145043/1152921504606846976), (2732165357/576460752303423488)), (7/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-20641994563/36893488147419103232), (909565385/36893488147419103232)), (17/36893488147419103232), by norm_num⟩
  | 10 => ⟨((4811541439/295147905179352825856), (-17679341559/295147905179352825856)), (5/73786976294838206464), by norm_num⟩
  | 11 => ⟨((3407680779/590295810358705651712), (552659175/147573952589676412928)), (23/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-2788151799/4722366482869645213696), (9121788269/18889465931478580854784)), (27/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (5499/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (5499/1280)))⁻¹=value ((2252800/33336601), (-7038720/33336601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/33336601), (-7038720/33336601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/39480601), (-7038720/39480601)), 0, by norm_num⟩
  | 1 => ⟨((17201070899200/1558717855321201), (27389067264000/1558717855321201)), 0, by norm_num⟩
  | 2 => ⟨((-18561307539/8796093022208), (1036077351/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1644683715/17592186044416), (-6822562341/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((7137179995/562949953421312), (10070949203/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-19991344381/9007199254740992), (1119388637/4503599627370496)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((3142413809/36028797018963968), (-15139081155/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((2079609479/144115188075855872), (10450330727/576460752303423488)), (11/576460752303423488), by norm_num⟩
  | 8 => ⟨((-10731919457/4611686018427387904), (1812214399/4611686018427387904)), (25/9223372036854775808), by norm_num⟩
  | 9 => ⟨((5877190219/73786976294838206464), (-16735442257/73786976294838206464)), (29/73786976294838206464), by norm_num⟩
  | 10 => ⟨((2404390185/147573952589676412928), (10788979555/590295810358705651712)), (33/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-5742792949/2361183241434822606848), (651287955/1180591620717411303424)), (37/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((333781363/4722366482869645213696), (-18435583579/75557863725914323419136)), (83/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (5499/1280)))⁻¹=value ((3891200/39480601), (-7038720/39480601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/39480601), (-7038720/39480601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-40777483878400/1316149042777201), (-43245895680000/1316149042777201)), 0, by norm_num⟩
  | 1 => ⟨((4932129903/549755813888), (-1815946941/549755813888)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-1269207787/17592186044416), (26603593745/17592186044416)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-6749572193/35184372088832), (-6442707161/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((11698924181/562949953421312), (-10485743425/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((5254414363/4503599627370496), (14901022275/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-15391062801/36028797018963968), (-765222525/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((6190944839/288230376151711744), (-13316962883/288230376151711744)), (5/144115188075855872), by norm_num⟩
  | 8 => ⟨((9402249815/2305843009213693952), (2505638557/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 9 => ⟨((-2947573709/4611686018427387904), (4638643257/18446744073709551616)), (29/36893488147419103232), by norm_num⟩
  | 10 => ⟨((690267/73786976294838206464), (-23073831335/295147905179352825856)), (35/295147905179352825856), by norm_num⟩
  | 11 => ⟨((19373516065/2361183241434822606848), (942496361/295147905179352825856)), (41/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-6243866323/9444732965739290427392), (3432671041/4722366482869645213696)), (3/1180591620717411303424), by norm_num⟩
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
  | 0 => ⟨((27/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((204800/1811163), (-782080/5433489)), 0, by norm_num⟩
  | 1 => ⟨((117080883200/29522802713121), (160169984000/9840934237707)), 0, by norm_num⟩
  | 2 => ⟨((-6137779851/4398046511104), (-5583755625/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((17534291473/140737488355328), (-9084122965/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-2700701367/1125899906842624), (28408271481/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 5 => ⟨((-869557255/1125899906842624), (-15959079735/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((30962606485/288230376151711744), (-49496503/9007199254740992)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((-6546327129/1152921504606846976), (9271529261/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 8 => ⟨((-2377120275/9223372036854775808), (-15925206215/18446744073709551616)), (21/18446744073709551616), by norm_num⟩
  | 9 => ⟨((11319276193/147573952589676412928), (8931646313/295147905179352825856)), (11/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-7690965615/1180591620717411303424), (8994261739/2361183241434822606848)), (23/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((3557826401/37778931862957161709568), (-25848548053/37778931862957161709568)), (3/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((13273021383/302231454903657293676544), (13739866075/302231454903657293676544)), (25/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (5499/1280)))⁻¹=value ((204800/1811163), (-782080/5433489)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((204800/1811163), (-782080/5433489))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4526057887/549755813888), (409050841/549755813888)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((4182262367/4398046511104), (-10112939291/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((706392993/2199023255552), (835245487/2199023255552)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-22621467019/281474976710656), (2660356039/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((1605696751/562949953421312), (-6727312379/562949953421312)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((11771857535/9007199254740992), (1223982963/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-916446925/4503599627370496), (6606332041/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 7 => ⟨((197572049/288230376151711744), (-4056061483/144115188075855872)), (27/1152921504606846976), by norm_num⟩
  | 8 => ⟨((3543482369/1152921504606846976), (1781449063/1152921504606846976)), (17/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-11844682867/36893488147419103232), (9380731717/36893488147419103232)), (11/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-3364380353/295147905179352825856), (-27344038397/590295810358705651712)), (13/147573952589676412928), by norm_num⟩
  | 11 => ⟨((6334668291/1180591620717411303424), (4621860725/4722366482869645213696)), (31/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-6496647131/18889465931478580854784), (2399790211/4722366482869645213696)), (73/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((35/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/61599001), (-7038720/61599001)), 0, by norm_num⟩
  | 1 => ⟨((-918322380800/3794436924198001), (50453544960000/3794436924198001)), 0, by norm_num⟩
  | 2 => ⟨((-13116824623/17592186044416), (-13853264111/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((24874513281/281474976710656), (905799279/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-11992154139/2251799813685248), (2736926933/562949953421312)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((72256947/2251799813685248), (-21153925429/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((2282659637/72057594037927936), (10374770861/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 7 => ⟨((-8991933117/2305843009213693952), (-655747607/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 8 => ⟨((17940498841/73786976294838206464), (-15218766453/73786976294838206464)), (15/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-2789247817/1180591620717411303424), (15283771627/590295810358705651712)), (7/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-792070677/590295810358705651712), (-15502906253/9444732965739290427392)), (53/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((25969462473/151115727451828646838272), (1423543383/75557863725914323419136)), (99/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-13389110227/1208925819614629174706176), (10544577303/1208925819614629174706176)), (23/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (5499/1280)))⁻¹=value ((7168000/61599001), (-7038720/61599001)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/61599001), (-7038720/61599001))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-15357957431/17592186044416), (9036440211/8796093022208)), (3/17592186044416), by norm_num⟩
  | 1 => ⟨((-5629208779/35184372088832), (-17095493965/35184372088832)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((16585985043/140737488355328), (3746686267/140737488355328)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-8765073623/562949953421312), (2331635979/140737488355328)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((-4837932435/4503599627370496), (-8038910103/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((19555410389/36028797018963968), (4449567837/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 6 => ⟨((-7470828537/144115188075855872), (16644072317/288230376151711744)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((-985541131/288230376151711744), (-11154452143/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((5930229493/4611686018427387904), (3618631933/18446744073709551616)), (31/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-6960386251/73786976294838206464), (73976199/576460752303423488)), (41/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-4995662849/590295810358705651712), (-10001832307/590295810358705651712)), (25/590295810358705651712), by norm_num⟩
  | 11 => ⟨((20746947709/9444732965739290427392), (29153719/9444732965739290427392)), (15/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-2076681199/18889465931478580854784), (8453313941/37778931862957161709568)), (9/9444732965739290427392), by norm_num⟩
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
  | 0 => ⟨((43/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/77573401), (-7038720/77573401)), 0, by norm_num⟩
  | 1 => ⟨((-14004550860800/6017632542706801), (61985783808000/6017632542706801)), 0, by norm_num⟩
  | 2 => ⟨((-5897327883/17592186044416), (-189739471/274877906944)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((7085299811/140737488355328), (1686901613/70368744177664)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-4441895773/1125899906842624), (259887803/281474976710656)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((3279474729/18014398509481984), (-16673741829/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 6 => ⟨((11861895/72057594037927936), (12332518849/576460752303423488)), (19/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-4519117671/4611686018427387904), (-11131357103/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 8 => ⟨((16288554535/147573952589676412928), (1774297627/73786976294838206464)), (29/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-542779783/73786976294838206464), (8600909513/2361183241434822606848)), (49/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((4765476475/18889465931478580854784), (-20419189489/37778931862957161709568)), (81/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((770774165/75557863725914323419136), (25462878387/604462909807314587353088)), (133/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-12041655165/4835703278458516698824704), (-4662272935/2417851639229258349412352)), (55/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (5499/1280)))⁻¹=value ((8806400/77573401), (-7038720/77573401)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/77573401), (-7038720/77573401))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-828982237/140737488355328), (1722609637/8796093022208)), (3/70368744177664), by norm_num⟩
  | 1 => ⟨((-4982142001/70368744177664), (-3660963231/70368744177664)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((24965044363/1125899906842624), (-4464276751/562949953421312)), (9/1125899906842624), by norm_num⟩
  | 3 => ⟨((-2619117231/2251799813685248), (5347600217/1125899906842624)), (11/4503599627370496), by norm_num⟩
  | 4 => ⟨((-1340585609/2251799813685248), (-2838038647/4503599627370496)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((9742579949/72057594037927936), (-953636463/36028797018963968)), (17/144115188075855872), by norm_num⟩
  | 6 => ⟨((-4103825127/576460752303423488), (21785173513/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-3964227009/2305843009213693952), (-2517524365/1152921504606846976)), (9/2305843009213693952), by norm_num⟩
  | 8 => ⟨((1662199575/4611686018427387904), (-3575839233/73786976294838206464)), (23/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-5113398209/295147905179352825856), (12464210315/295147905179352825856)), (15/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-8100475515/2361183241434822606848), (-10244422001/2361183241434822606848)), (19/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((378511199/590295810358705651712), (-2046480305/18889465931478580854784)), (93/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-7150629541/302231454903657293676544), (21342907693/302231454903657293676544)), (111/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((51/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/32274867), (-782080/10758289)), 0, by norm_num⟩
  | 1 => ⟨((-3308348211200/1041667039867689), (2722889728000/347222346622563)), 0, by norm_num⟩
  | 2 => ⟨((-500201879/4398046511104), (-9471780027/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((904390423/35184372088832), (14020853919/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-20641671291/9007199254740992), (-3684435503/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((9978118605/72057594037927936), (-137888191/2251799813685248)), (7/144115188075855872), by norm_num⟩
  | 6 => ⟨((-12089762095/2305843009213693952), (9610784719/1152921504606846976)), (11/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-23289789/1152921504606846976), (-23618947727/36893488147419103232)), (17/36893488147419103232), by norm_num⟩
  | 8 => ⟨((7189552571/295147905179352825856), (9974713575/295147905179352825856)), (13/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-6002716381/2361183241434822606848), (-4426861795/4722366482869645213696)), (39/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((12935041975/75557863725914323419136), (-790402299/18889465931478580854784)), (57/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-9324096841/1208925819614629174706176), (10250991017/1208925819614629174706176)), (21/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((2084963609/19342813113834066795298816), (-14269039571/19342813113834066795298816)), (61/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (5499/1280)))⁻¹=value ((3481600/32274867), (-782080/10758289)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/32274867), (-782080/10758289))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7656769659/562949953421312), (379180473/17592186044416)), (5/562949953421312), by norm_num⟩
  | 1 => ⟨((-7282628635/562949953421312), (-1276153115/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((5751971011/2251799813685248), (-3238585145/1125899906842624)), (9/4503599627370496), by norm_num⟩
  | 3 => ⟨((3361192569/18014398509481984), (7610218529/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 4 => ⟨((-679170151/4503599627370496), (-9149814655/144115188075855872)), (11/72057594037927936), by norm_num⟩
  | 5 => ⟨((6658871993/288230376151711744), (-8497698949/576460752303423488)), (9/288230376151711744), by norm_num⟩
  | 6 => ⟨((-30146723/288230376151711744), (19326070623/4611686018427387904)), (7/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-9055058265/18446744073709551616), (-12558792743/36893488147419103232)), (41/36893488147419103232), by norm_num⟩
  | 8 => ⟨((21902140907/295147905179352825856), (-9123425353/295147905179352825856)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-123804945/73786976294838206464), (6008920343/590295810358705651712)), (71/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-18228077721/18889465931478580854784), (-15653109133/18889465931478580854784)), (91/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((21679597571/151115727451828646838272), (-7356390515/151115727451828646838272)), (113/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-2047405945/604462909807314587353088), (10383442243/604462909807314587353088)), (69/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((59/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/119352601), (-7038720/119352601)), 0, by norm_num⟩
  | 1 => ⟨((-48230071500800/14245043365465201), (85050261504000/14245043365465201)), 0, by norm_num⟩
  | 2 => ⟨((-328449603/70368744177664), (-28292584621/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((3403567275/281474976710656), (2844957637/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-5441068153/4503599627370496), (-12010296031/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((11646806749/144115188075855872), (-540905643/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 6 => ⟨((-18610678271/4611686018427387904), (11427859491/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((4840750627/36893488147419103232), (-18036001757/73786976294838206464)), (17/73786976294838206464), by norm_num⟩
  | 8 => ⟨((83507609/147573952589676412928), (19175316871/1180591620717411303424)), (23/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-9587859723/18889465931478580854784), (-15215212303/18889465931478580854784)), (15/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((14943798049/302231454903657293676544), (7799558105/302231454903657293676544)), (39/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-31566005833/9671406556917033397649408), (733395979/4835703278458516698824704)), (101/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((12436897753/77371252455336267181195264), (-8040304615/77371252455336267181195264)), (33/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (5499/1280)))⁻¹=value ((12083200/119352601), (-7038720/119352601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/119352601), (-7038720/119352601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5962987765/2251799813685248), (6214927749/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 1 => ⟨((-13972617929/9007199254740992), (2956171111/4503599627370496)), (11/9007199254740992), by norm_num⟩
  | 2 => ⟨((5337268519/36028797018963968), (-9382292543/18014398509481984)), (15/36028797018963968), by norm_num⟩
  | 3 => ⟨((5517875597/72057594037927936), (15170446767/144115188075855872)), (9/72057594037927936), by norm_num⟩
  | 4 => ⟨((-29966763905/1152921504606846976), (-696986737/1152921504606846976)), (37/1152921504606846976), by norm_num⟩
  | 5 => ⟨((3231737105/1152921504606846976), (-8279525453/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((3699301283/18446744073709551616), (12817605313/18446744073709551616)), (51/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-14818107495/147573952589676412928), (-5131608573/147573952589676412928)), (39/147573952589676412928), by norm_num⟩
  | 8 => ⟨((6964252499/590295810358705651712), (-10278702425/1180591620717411303424)), (53/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((212460479/2361183241434822606848), (18116140291/9444732965739290427392)), (35/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-15691810851/75557863725914323419136), (-9174712837/75557863725914323419136)), (91/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((486337185/18889465931478580854784), (-8079446131/604462909807314587353088)), (57/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-577875801/2417851639229258349412352), (254979957/75557863725914323419136)), (35/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((67/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/145157401), (-7038720/145157401)), 0, by norm_num⟩
  | 1 => ⟨((-69369363660800/21070671065074801), (96582500352000/21070671065074801)), 0, by norm_num⟩
  | 2 => ⟨((3129445469/70368744177664), (-10431071195/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((1431573991/281474976710656), (16990619083/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-10921449499/18014398509481984), (-5313754133/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((12381804297/288230376151711744), (7600399779/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-21675417989/9223372036854775808), (482334769/1152921504606846976)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((14894797429/147573952589676412928), (-11326432401/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-6870162473/2361183241434822606848), (7171720673/1180591620717411303424)), (15/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-368694729/37778931862957161709568), (-13512069689/37778931862957161709568)), (35/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((5520449171/604462909807314587353088), (20150493213/1208925819614629174706176)), (41/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-4041577877/4835703278458516698824704), (-5477728709/9671406556917033397649408)), (3/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((16475360135/309485009821345068724781056), (503402019/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (5499/1280)))⁻¹=value ((13721600/145157401), (-7038720/145157401)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/145157401), (-7038720/145157401))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5714861265/18014398509481984), (36791789/18014398509481984)), (17/72057594037927936), by norm_num⟩
  | 1 => ⟨((-4678517345/36028797018963968), (10438668949/72057594037927936)), (7/36028797018963968), by norm_num⟩
  | 2 => ⟨((-1243150993/144115188075855872), (-19141806825/288230376151711744)), (21/288230376151711744), by norm_num⟩
  | 3 => ⟨((16556987301/1152921504606846976), (5284586157/576460752303423488)), (13/576460752303423488), by norm_num⟩
  | 4 => ⟨((-1952669099/576460752303423488), (5156358749/4611686018427387904)), (7/1152921504606846976), by norm_num⟩
  | 5 => ⟨((8258719769/36893488147419103232), (-22516785269/36893488147419103232)), (49/36893488147419103232), by norm_num⟩
  | 6 => ⟨((8392075951/147573952589676412928), (6657986149/73786976294838206464)), (5/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-18952566099/1180591620717411303424), (-1539672479/1180591620717411303424)), (31/590295810358705651712), by norm_num⟩
  | 8 => ⟨((14010771277/9444732965739290427392), (-4067537803/2361183241434822606848)), (11/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1382100381/18889465931478580854784), (22239903993/75557863725914323419136)), (59/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-5457447839/151115727451828646838272), (-4093999311/302231454903657293676544)), (155/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((4619313437/1208925819614629174706176), (-13285204645/4835703278458516698824704)), (197/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((65414493/2417851639229258349412352), (21396313773/38685626227668133590597632)), (61/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((75/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/58079667), (-782080/19359889)), 0, by norm_num⟩
  | 1 => ⟨((-10354778931200/3373247718830889), (4004249600000/1124415906276963)), 0, by norm_num⟩
  | 2 => ⟨((4459472515/70368744177664), (-15408667933/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((1834712141/1125899906842624), (12307973131/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-10543086631/36028797018963968), (-4043559507/9007199254740992)), (5/36028797018963968), by norm_num⟩
  | 5 => ⟨((6182863/281474976710656), (7999424257/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-23030596701/18446744073709551616), (-1549289897/9223372036854775808)), (13/18446744073709551616), by norm_num⟩
  | 7 => ⟨((8621720711/147573952589676412928), (-5257685607/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5230789481/2361183241434822606848), (580036059/295147905179352825856)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((8757301845/151115727451828646838272), (-2481485611/18889465931478580854784)), (1/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((479314305/4835703278458516698824704), (8415226107/1208925819614629174706176)), (67/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-2804101809/19342813113834066795298816), (-11792026581/38685626227668133590597632)), (9/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((15532024857/1237940039285380274899124224), (3251877077/309485009821345068724781056)), (75/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (5499/1280)))⁻¹=value ((5120000/58079667), (-782080/19359889)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/58079667), (-782080/19359889))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16168914767/576460752303423488), (-910477819/72057594037927936)), (9/288230376151711744), by norm_num⟩
  | 1 => ⟨((-7581957511/1152921504606846976), (22066701441/1152921504606846976)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((-4081318745/1152921504606846976), (-14947594681/2305843009213693952)), (13/1152921504606846976), by norm_num⟩
  | 3 => ⟨((1108696327/576460752303423488), (2039442885/4611686018427387904)), (33/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-6403747677/18446744073709551616), (9398965247/36893488147419103232)), (9/9223372036854775808), by norm_num⟩
  | 5 => ⟨((1544903753/295147905179352825856), (-23932500747/295147905179352825856)), (33/147573952589676412928), by norm_num⟩
  | 6 => ⟨((2970756239/295147905179352825856), (11023167001/1180591620717411303424)), (55/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-19835047765/9444732965739290427392), (3072338869/9444732965739290427392)), (87/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((11120582969/75557863725914323419136), (-10145367049/37778931862957161709568)), (63/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((10443633119/604462909807314587353088), (5712409103/151115727451828646838272)), (43/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-25416207415/4835703278458516698824704), (-4970013/4722366482869645213696)), (57/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((1157626329/2417851639229258349412352), (-8826496197/19342813113834066795298816)), (147/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((993543799/77371252455336267181195264), (23968965391/309485009821345068724781056)), (367/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((83/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/206597401), (-7038720/206597401)), 0, by norm_num⟩
  | 1 => ⟨((-119701011660800/42682486099954801), (119646978048000/42682486099954801)), 0, by norm_num⟩
  | 2 => ⟨((9516712961/140737488355328), (-11476694939/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-999089/281474976710656), (17702309057/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-301227733/2251799813685248), (-23308497573/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((6348859189/576460752303423488), (1589366169/144115188075855872)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-11823487503/18446744073709551616), (-4908397499/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((9120316305/295147905179352825856), (4117885/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-24021793607/18889465931478580854784), (310049195/590295810358705651712)), (23/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((819218615/18889465931478580854784), (-13077940575/302231454903657293676544)), (11/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-2531581303/2417851639229258349412352), (47581079/18889465931478580854784)), (21/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((25458659/154742504910672534362390528), (-9397661319/77371252455336267181195264)), (5/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((1276514189/618970019642690137449562112), (12378456153/2475880078570760549798248448)), (19/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (5499/1280)))⁻¹=value ((16998400/206597401), (-7038720/206597401)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/206597401), (-7038720/206597401))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1082186379/576460752303423488), (-4600673423/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 1 => ⟨((625001561/9223372036854775808), (4410840797/2305843009213693952)), (33/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-631215711/1152921504606846976), (-9044427055/18446744073709551616)), (7/4611686018427387904), by norm_num⟩
  | 3 => ⟨((15066252615/73786976294838206464), (-2699969817/147573952589676412928)), (73/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-8255679849/295147905179352825856), (10926155797/295147905179352825856)), (41/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-2139033321/1180591620717411303424), (-2611875347/295147905179352825856)), (77/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((3238472375/2361183241434822606848), (7163780033/9444732965739290427392)), (33/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-4364511453/18889465931478580854784), (3418071919/37778931862957161709568)), (53/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((1650861943/151115727451828646838272), (-10507926691/302231454903657293676544)), (157/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((6896419311/2417851639229258349412352), (20010137545/4835703278458516698824704)), (219/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-6345752069/9671406556917033397649408), (-564198239/19342813113834066795298816)), (147/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((7943889923/154742504910672534362390528), (-4938933613/77371252455336267181195264)), (3/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((6612264357/2475880078570760549798248448), (1460046707/154742504910672534362390528)), (483/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((91/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1433600/18633277), (-541440/18633277)), 0, by norm_num⟩
  | 1 => ⟨((-881025843200/347199011758729), (776208384000/347199011758729)), 0, by norm_num⟩
  | 2 => ⟨((4583426991/70368744177664), (-17292317427/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-3244817985/4503599627370496), (25548757899/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-3941914635/72057594037927936), (-4119895129/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((12514241393/2305843009213693952), (18453708485/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-2998076225/9223372036854775808), (-4224597879/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((18690776383/1180591620717411303424), (4825477321/1180591620717411303424)), (7/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-6312964373/9444732965739290427392), (171850055/2361183241434822606848)), (3/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((14903366273/604462909807314587353088), (-3781233659/302231454903657293676544)), (21/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-14830107305/19342813113834066795298816), (2029791301/2417851639229258349412352)), (9/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((1338289579/77371252455336267181195264), (-3360534357/77371252455336267181195264)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-340188683/9903520314283042199192993792), (19036103853/9903520314283042199192993792)), (55/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (5499/1280)))⁻¹=value ((1433600/18633277), (-541440/18633277)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((1433600/18633277), (-541440/18633277))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6379469941/73786976294838206464), (-15351942899/73786976294838206464)), (1/2305843009213693952), by norm_num⟩
  | 1 => ⟨((8927455149/147573952589676412928), (22794951177/147573952589676412928)), (59/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-4496658147/73786976294838206464), (-7932617513/295147905179352825856)), (27/147573952589676412928), by norm_num⟩
  | 3 => ⟨((2643456439/147573952589676412928), (-8491148747/1180591620717411303424)), (9/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-3921784897/2361183241434822606848), (19823956169/4722366482869645213696)), (21/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-3717791977/9444732965739290427392), (-15372656597/18889465931478580854784)), (81/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((23351949641/151115727451828646838272), (6662764133/151115727451828646838272)), (141/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-13136799613/604462909807314587353088), (8597850123/604462909807314587353088)), (115/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((1111286447/2417851639229258349412352), (-4660804595/1208925819614629174706176)), (87/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((1828001277/4835703278458516698824704), (7552872747/19342813113834066795298816)), (247/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-11070936711/154742504910672534362390528), (282125387/38685626227668133590597632)), (21/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((11738334729/2475880078570760549798248448), (-19121131821/2475880078570760549798248448)), (443/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((253447363/618970019642690137449562112), (10045179321/9903520314283042199192993792)), (141/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((99/8), (5499/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/31238289), (-782080/31238289)), 0, by norm_num⟩
  | 1 => ⟨((-743909785600/325276899882507), (1761869824000/975830699647521)), 0, by norm_num⟩
  | 2 => ⟨((8425142305/140737488355328), (-13191637119/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-138663885/140737488355328), (18596283757/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1164611185/72057594037927936), (-2904383661/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((1499375023/576460752303423488), (12938564173/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-6051588927/36893488147419103232), (-12526920407/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1186463605/147573952589676412928), (300192385/73786976294838206464)), (3/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-6438076821/18889465931478580854784), (-3479933313/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((7777171675/604462909807314587353088), (-1575088919/604462909807314587353088)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-4171436357/9671406556917033397649408), (4932782709/19342813113834066795298816)), (13/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((15301214941/1237940039285380274899124224), (-18067434389/1237940039285380274899124224)), (41/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-5209093989/19807040628566084398385987584), (6744170959/9903520314283042199192993792)), (33/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (5499/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (5499/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (5499/1280)))⁻¹=value ((2252800/31238289), (-782080/31238289)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/31238289), (-782080/31238289))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1211447851/1180591620717411303424), (-5067385453/295147905179352825856)), (51/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((9926138969/1180591620717411303424), (12109152059/1180591620717411303424)), (49/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((-1623111267/295147905179352825856), (-1598851459/2361183241434822606848)), (93/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((778313583/590295810358705651712), (-2388501353/2361183241434822606848)), (65/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-3744950109/75557863725914323419136), (30019230473/75557863725914323419136)), (153/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-1962567977/37778931862957161709568), (-9638382155/151115727451828646838272)), (19/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((18036743551/1208925819614629174706176), (580529311/604462909807314587353088)), (17/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-17033291263/9671406556917033397649408), (16654382515/9671406556917033397649408)), (7/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-1657755965/77371252455336267181195264), (-28912092857/77371252455336267181195264)), (345/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((13149353271/309485009821345068724781056), (9873074365/309485009821345068724781056)), (249/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-17104202855/2475880078570760549798248448), (2102827729/1237940039285380274899124224)), (343/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((7455327733/19807040628566084398385987584), (-16308724305/19807040628566084398385987584)), (457/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((8185562045/158456325028528675187087900672), (15417521165/158456325028528675187087900672)), (589/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2884381561/274877906944), (-695817143/549755813888)), (3/8589934592), by norm_num⟩
  | 1 => ⟨((-15124461079/2199023255552), (-4462263207/549755813888)), (959/1099511627776), by norm_num⟩
  | 2 => ⟨((316868923/2199023255552), (-22263550313/4398046511104)), (4547/4398046511104), by norm_num⟩
  | 3 => ⟨((8816272221/8796093022208), (-2464820343/2199023255552)), (3575/4398046511104), by norm_num⟩
  | 4 => ⟨((21397417613/70368744177664), (-4275649641/70368744177664)), (8485/17592186044416), by norm_num⟩
  | 5 => ⟨((25281931529/562949953421312), (2223910265/140737488355328)), (65127/281474976710656), by norm_num⟩
  | 6 => ⟨((10468672761/2251799813685248), (4424529063/1125899906842624)), (6591/70368744177664), by norm_num⟩
  | 7 => ⟨((8039507049/18014398509481984), (5654340607/9007199254740992)), (593111/18014398509481984), by norm_num⟩
  | 8 => ⟨((7929731895/288230376151711744), (25984505681/288230376151711744)), (92453/9007199254740992), by norm_num⟩
  | 9 => ⟨((-1482368333/2305843009213693952), (21867216435/2305843009213693952)), (1662357/576460752303423488), by norm_num⟩
  | 10 => ⟨((-4125743417/18446744073709551616), (14326518101/18446744073709551616)), (13641093/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-8320207747/295147905179352825856), (21354864867/295147905179352825856)), (6452493/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-11432265797/2361183241434822606848), (6828168155/1180591620717411303424)), (11358243/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2884381561/274877906944), (-695817143/549755813888)), (769/2199023255552), by norm_num⟩
  | 1 => ⟨((-15124461079/2199023255552), (-4462263207/549755813888)), (1919/2199023255552), by norm_num⟩
  | 2 => ⟨((316868923/2199023255552), (-22263550313/4398046511104)), (1137/1099511627776), by norm_num⟩
  | 3 => ⟨((8816272221/8796093022208), (-2464820343/2199023255552)), (7151/8796093022208), by norm_num⟩
  | 4 => ⟨((21397417613/70368744177664), (-4275649641/70368744177664)), (33943/70368744177664), by norm_num⟩
  | 5 => ⟨((25281931529/562949953421312), (2223910265/140737488355328)), (130277/562949953421312), by norm_num⟩
  | 6 => ⟨((10468672761/2251799813685248), (4424529063/1125899906842624)), (211003/2251799813685248), by norm_num⟩
  | 7 => ⟨((8039507049/18014398509481984), (5654340607/9007199254740992)), (74229/2251799813685248), by norm_num⟩
  | 8 => ⟨((7929731895/288230376151711744), (25984505681/288230376151711744)), (1485013/144115188075855872), by norm_num⟩
  | 9 => ⟨((-1482368333/2305843009213693952), (21867216435/2305843009213693952)), (3370831/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-4125743417/18446744073709551616), (14326518101/18446744073709551616)), (14378963/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-8320207747/295147905179352825856), (21354864867/295147905179352825856)), (63425861/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-11432265797/2361183241434822606848), (6828168155/1180591620717411303424)), (92656637/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile019Gamma
