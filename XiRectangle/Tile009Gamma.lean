/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile009Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2679/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2679/640))
  have he : value ((3/4), (2679/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/300271441), (-3429120/300271441)), 0, by norm_num⟩
  | 1 => ⟨((-234223500492800/90162938280216481), (75144364032000/90162938280216481)), 0, by norm_num⟩
  | 2 => ⟨((50684179671/562949953421312), (-25470630047/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-6816039443/2251799813685248), (4875291039/2251799813685248)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((28272233361/288230376151711744), (-55505275127/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-27941613719/9223372036854775808), (75143644913/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((6440346867/73786976294838206464), (-3061060459/18446744073709551616)), (5/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-5282911233/2361183241434822606848), (61896026167/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((13365054621/302231454903657293676544), (-4758453553/18889465931478580854784)), (3/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-847220871/4835703278458516698824704), (91342842855/9671406556917033397649408)), (17/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-14711715497/309485009821345068724781056), (-13370974999/38685626227668133590597632)), (3/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((4590460343/1237940039285380274899124224), (30553706159/2475880078570760549798248448)), (17/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-16303080833/79228162514264337593543950336), (-67998124835/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (2679/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (2679/1280)))⁻¹=value ((21913600/300271441), (-3429120/300271441)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/300271441), (-3429120/300271441))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22380931613/8589934592), (5333483873/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((10956800/300271441), (-1714560/300271441)), 0, by norm_num⟩
  | 2 => ⟨((-58555875123200/90162938280216481), (18786091008000/90162938280216481)), 0, by norm_num⟩
  | 3 => ⟨((16894726557/1125899906842624), (-33960840063/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-6816039443/18014398509481984), (4875291039/18014398509481984)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((22617786689/2305843009213693952), (-22202110051/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-37255484959/147573952589676412928), (50095763275/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((14720792839/2361183241434822606848), (-55973676965/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-5282911233/37778931862957161709568), (61896026167/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1485006069/604462909807314587353088), (-67675783865/4835703278458516698824704)), (11/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-677776697/77371252455336267181195264), (18268568571/38685626227668133590597632)), (7/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-2674857363/1237940039285380274899124224), (-77794763631/4951760157141521099596496896)), (19/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((24482455163/158456325028528675187087900672), (81476549757/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (57/20480)), 0, by norm_num⟩
  | 45 => ⟨((106086059393/4080638361600), (-113259/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-50754224252839/1915179604377600), (2380963358867/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((29772749697/1099511627776), (-18144892323/4398046511104)), (1/4398046511104), by norm_num⟩
  | 42 => ⟨((-60940108411/2199023255552), (4638813769/1099511627776)), (1/2199023255552), by norm_num⟩
  | 41 => ⟨((31209544277/1099511627776), (-2373429919/549755813888)), (1/2199023255552), by norm_num⟩
  | 40 => ⟨((-31987167221/1099511627776), (4861319247/1099511627776)), (1/2199023255552), by norm_num⟩
  | 39 => ⟨((65609177267/2199023255552), (-2490909513/549755813888)), (1/2199023255552), by norm_num⟩
  | 38 => ⟨((-4208105609/137438953472), (5108515863/1099511627776)), (1/2199023255552), by norm_num⟩
  | 37 => ⟨((69142842677/2199023255552), (-1310458163/274877906944)), (1/2199023255552), by norm_num⟩
  | 36 => ⟨((-17764088239/549755813888), (5382294701/1099511627776)), (1/2199023255552), by norm_num⟩
  | 35 => ⟨((73078796953/2199023255552), (-5530492919/1099511627776)), (1/2199023255552), by norm_num⟩
  | 34 => ⟨((-37609875547/1099511627776), (11374170383/2199023255552)), (1/1099511627776), by norm_num⟩
  | 33 => ⟨((19372486829/549755813888), (-11705611605/2199023255552)), (1/2199023255552), by norm_num⟩
  | 32 => ⟨((-39950726881/1099511627776), (6028477145/1099511627776)), (1/2199023255552), by norm_num⟩
  | 31 => ⟨((20616972381/549755813888), (-6215023463/1099511627776)), (1/2199023255552), by norm_num⟩
  | 30 => ⟨((-42602341037/1099511627776), (6413487151/1099511627776)), (1/2199023255552), by norm_num⟩
  | 29 => ⟨((11016172219/274877906944), (-6625048265/1099511627776)), (1/2199023255552), by norm_num⟩
  | 28 => ⟨((-91262018505/2199023255552), (13702096061/2199023255552)), (1/1099511627776), by norm_num⟩
  | 27 => ⟨((94625601993/2199023255552), (-14186034685/2199023255552)), (1/1099511627776), by norm_num⟩
  | 26 => ⟨((-98246647393/2199023255552), (14705423061/2199023255552)), (1/1099511627776), by norm_num⟩
  | 25 => ⟨((102155896377/2199023255552), (-15264306145/2199023255552)), (1/1099511627776), by norm_num⟩
  | 24 => ⟨((-6649324281/137438953472), (7933684449/1099511627776)), (1/1099511627776), by norm_num⟩
  | 23 => ⟨((55494281899/1099511627776), (-16520068139/2199023255552)), (1/1099511627776), by norm_num⟩
  | 22 => ⟨((-58001832313/1099511627776), (8614399203/1099511627776)), (1/1099511627776), by norm_num⟩
  | 21 => ⟨((1898336497/34359738368), (-4500275637/549755813888)), (1/1099511627776), by norm_num⟩
  | 20 => ⟨((-15941120241/274877906944), (4711485437/549755813888)), (1/1099511627776), by norm_num⟩
  | 19 => ⟨((33548884613/549755813888), (-9887022785/1099511627776)), (1/1099511627776), by norm_num⟩
  | 18 => ⟨((-70798880227/1099511627776), (5199592781/549755813888)), (1/1099511627776), by norm_num⟩
  | 17 => ⟨((9366534089/137438953472), (-5483678311/549755813888)), (1/1099511627776), by norm_num⟩
  | 16 => ⟨((-39789203405/549755813888), (5800631759/549755813888)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((84839039927/1099511627776), (-6156513605/549755813888)), (1/1099511627776), by norm_num⟩
  | 14 => ⟨((-45422388003/549755813888), (3279486809/274877906944)), (1/1099511627776), by norm_num⟩
  | 13 => ⟨((97766072733/1099511627776), (-54826633/4294967296)), (1/1099511627776), by norm_num⟩
  | 12 => ⟨((-105829708417/1099511627776), (7545776013/549755813888)), (1/1099511627776), by norm_num⟩
  | 11 => ⟨((115344154889/1099511627776), (-4079899947/274877906944)), (1/1099511627776), by norm_num⟩
  | 10 => ⟨((-15842504677/137438953472), (1110354145/68719476736)), (1/549755813888), by norm_num⟩
  | 9 => ⟨((2197457961/17179869184), (-4873403309/274877906944)), (1/549755813888), by norm_num⟩
  | 8 => ⟨((-78981145927/549755813888), (1349688393/68719476736)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((1407530645/8589934592), (-12103032907/549755813888)), (1/274877906944), by norm_num⟩
  | 6 => ⟨((-6551364775/34359738368), (13769324455/549755813888)), (1/274877906944), by norm_num⟩
  | 5 => ⟨((62673661225/274877906944), (-7985415769/274877906944)), (1/274877906944), by norm_num⟩
  | 4 => ⟨((-77957297677/274877906944), (4754241587/137438953472)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((12896503531/34359738368), (-11757622263/274877906944)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((-76413796679/137438953472), (3856243585/68719476736)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((74483358663/68719476736), (-5630530229/68719476736)), (1/68719476736), by norm_num⟩
  | 0 => ⟨((-45933573169/274877906944), (21333935491/137438953472)), (1/137438953472), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (2679/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (2679/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (2679/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((22380931613/8589934592), (5333483873/34359738368)), (1/34359738368), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (2679/1280))) (z:=((-21/128), (2679/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((22380931613/8589934592), (5333483873/34359738368))) (r:=(1/34359738368)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((71340947687/2147483648), (4000608855/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((7664355623/4294967296), (1382419783/17179869184)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((851781468748800/90162938280216481), (-138101395974240/90162938280216481)), 0, by norm_num⟩
  | 3 => ⟨((-8144732453/70368744177664), (21671658561/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((74394945671/36028797018963968), (-1213629097/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-49277099105/1152921504606846976), (18376195081/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((8703496135/9223372036854775808), (-35864783813/36893488147419103232)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-49938093515/2361183241434822606848), (71245720125/2361183241434822606848)), (93/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((8681124229/18889465931478580854784), (-71447683509/75557863725914323419136)), (117/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-10876848261/1208925819614629174706176), (71937635889/2417851639229258349412352)), (147/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((9842927189/77371252455336267181195264), (-72409195663/77371252455336267181195264)), (97/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((1689000347/2475880078570760549798248448), (72593617655/2475880078570760549798248448)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-6626783377/39614081257132168796771975168), (-36116156599/39614081257132168796771975168)), (333/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((42618353895/2147483648), (23015638507/4294967296)), (5/4294967296), by norm_num⟩
  | 1 => ⟨((5516871975/4294967296), (1382419783/17179869184)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((851781468748800/90162938280216481), (-138101395974240/90162938280216481)), 0, by norm_num⟩
  | 3 => ⟨((-8144732453/70368744177664), (21671658561/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((74394945671/36028797018963968), (-1213629097/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-49277099105/1152921504606846976), (18376195081/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((8703496135/9223372036854775808), (-35864783813/36893488147419103232)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-49938093515/2361183241434822606848), (71245720125/2361183241434822606848)), (93/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((8681124229/18889465931478580854784), (-71447683509/75557863725914323419136)), (117/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-10876848261/1208925819614629174706176), (71937635889/2417851639229258349412352)), (147/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((9842927189/77371252455336267181195264), (-72409195663/77371252455336267181195264)), (97/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((1689000347/2475880078570760549798248448), (72593617655/2475880078570760549798248448)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-6626783377/39614081257132168796771975168), (-36116156599/39614081257132168796771975168)), (333/79228162514264337593543950336), by norm_num⟩
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
  | 0 => ⟨((126297950309/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((126297950309/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((89183518737/4294967296), (23015638507/4294967296)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((5516871975/4294967296), (1382419783/17179869184)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((851781468748800/90162938280216481), (-138101395974240/90162938280216481)), 0, by norm_num⟩
  | 3 => ⟨((-8144732453/70368744177664), (21671658561/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((74394945671/36028797018963968), (-1213629097/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-49277099105/1152921504606846976), (18376195081/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((8703496135/9223372036854775808), (-35864783813/36893488147419103232)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-49938093515/2361183241434822606848), (71245720125/2361183241434822606848)), (93/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((8681124229/18889465931478580854784), (-71447683509/75557863725914323419136)), (117/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-10876848261/1208925819614629174706176), (71937635889/2417851639229258349412352)), (147/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((9842927189/77371252455336267181195264), (-72409195663/77371252455336267181195264)), (97/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((1689000347/2475880078570760549798248448), (72593617655/2475880078570760549798248448)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-6626783377/39614081257132168796771975168), (-36116156599/39614081257132168796771975168)), (333/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((468447000985600/90162938280216481), (-150288728064000/90162938280216481)), 0, by norm_num⟩
  | 1 => ⟨((-50684179671/140737488355328), (25470630047/140737488355328)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((20448118329/1125899906842624), (-14625873117/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-28272233361/36028797018963968), (55505275127/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((34927017149/1152921504606846976), (-46964778071/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((-19321040601/18446744073709551616), (73465451017/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 6 => ⟨((4622547329/147573952589676412928), (-54159022897/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-13365054621/18889465931478580854784), (4758453553/1180591620717411303424)), (5/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((119140435/37778931862957161709568), (-25690174553/151115727451828646838272)), (1/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((9194822185/9671406556917033397649408), (66854874995/9671406556917033397649408)), (13/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-12623765943/154742504910672534362390528), (-84022691937/309485009821345068724781056)), (5/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((12227310625/2475880078570760549798248448), (25499296813/2475880078570760549798248448)), (1/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-41029534619/158456325028528675187087900672), (-59671184229/158456325028528675187087900672)), (23/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((50684179671/140737488355328), (-25470630047/140737488355328)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-20448118329/562949953421312), (14625873117/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((42408350041/18014398509481984), (-41628956345/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 3 => ⟨((-34927017149/288230376151711744), (46964778071/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((24151300751/4611686018427387904), (-22957953443/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-13867641987/73786976294838206464), (81238534345/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((5847211397/1180591620717411303424), (-66618349743/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-119140435/4722366482869645213696), (102760698213/75557863725914323419136)), (15/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-5172087479/604462909807314587353088), (-37605867185/604462909807314587353088)), (13/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((31559414857/38685626227668133590597632), (52514182461/19342813113834066795298816)), (11/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-16812552109/309485009821345068724781056), (-17530766559/154742504910672534362390528)), (19/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((7693037741/2475880078570760549798248448), (11188347043/2475880078570760549798248448)), (15/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-25730289907/158456325028528675187087900672), (-13601704557/79228162514264337593543950336)), (25/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6816039443/281474976710656), (-4875291039/281474976710656)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-28272233361/9007199254740992), (55505275127/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 2 => ⟨((34927017149/144115188075855872), (-23482389035/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((-32201734335/2305843009213693952), (61221209181/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 4 => ⟨((5778184161/9223372036854775808), (-67698778621/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-5847211397/295147905179352825856), (66618349743/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 6 => ⟨((2223954787/18889465931478580854784), (-119887481249/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((6896116639/151115727451828646838272), (100282312493/302231454903657293676544)), (17/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-23669561143/4835703278458516698824704), (-19692818423/1208925819614629174706176)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((14010460091/38685626227668133590597632), (29217944265/38685626227668133590597632)), (15/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-28207805051/1237940039285380274899124224), (-20511969579/618970019642690137449562112)), (13/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((51460579813/39614081257132168796771975168), (54406818229/39614081257132168796771975168)), (23/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-21884433397/316912650057057350374175801344), (-16914441565/316912650057057350374175801344)), (19/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((28272233361/18014398509481984), (-55505275127/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((-34927017149/144115188075855872), (46964778071/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 2 => ⟨((24151300751/1152921504606846976), (-45915906885/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 3 => ⟨((-23112736645/18446744073709551616), (67698778621/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 4 => ⟨((3654507123/73786976294838206464), (-41636468589/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-833983045/2361183241434822606848), (11239451367/590295810358705651712)), (13/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-6034102059/37778931862957161709568), (-10968377929/9444732965739290427392)), (7/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((23669561143/1208925819614629174706176), (19692818423/302231454903657293676544)), (1/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-31523535205/19342813113834066795298816), (-65740374597/19342813113834066795298816)), (1/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((35259756313/309485009821345068724781056), (12819980987/77371252455336267181195264)), (17/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-17689574311/2475880078570760549798248448), (-9351171883/1237940039285380274899124224)), (15/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((2051665631/4951760157141521099596496896), (50743324695/158456325028528675187087900672)), (7/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-57288790997/2535301200456458802993406410752), (-31503437817/2535301200456458802993406410752)), (25/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((27941613719/288230376151711744), (-75143644913/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 1 => ⟨((-19321040601/1152921504606846976), (73465451017/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 2 => ⟨((27735283973/18446744073709551616), (-10154816793/2305843009213693952)), (9/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-5847211397/73786976294838206464), (33309174871/73786976294838206464)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((833983045/1180591620717411303424), (-11239451367/295147905179352825856)), (13/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((7240922471/18889465931478580854784), (105296428117/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-258885825/4722366482869645213696), (-430780403/2361183241434822606848)), (11/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((6304707041/1208925819614629174706176), (52592299677/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-15866890341/38685626227668133590597632), (-46151931553/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((17689574311/618970019642690137449562112), (37404687533/1237940039285380274899124224)), (1/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-72218630211/39614081257132168796771975168), (-55817657165/39614081257132168796771975168)), (15/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((17186637299/158456325028528675187087900672), (9451031345/158456325028528675187087900672)), (15/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-61753075543/10141204801825835211973625643008), (-22370055849/10141204801825835211973625643008)), (7/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6440346867/1152921504606846976), (-3061060459/288230376151711744)), (5/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-4622547329/4611686018427387904), (54159022897/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((11694422793/147573952589676412928), (-33309174871/73786976294838206464)), (9/147573952589676412928), by norm_num⟩
  | 3 => ⟨((-555988697/590295810358705651712), (119887481247/2361183241434822606848)), (17/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-6034102059/9444732965739290427392), (-87747023431/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((258885825/2361183241434822606848), (430780403/1180591620717411303424)), (3/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-29421966191/2417851639229258349412352), (-15339420739/604462909807314587353088)), (1/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((5288963447/4835703278458516698824704), (61535908737/38685626227668133590597632)), (19/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-53068722933/618970019642690137449562112), (-28053515649/309485009821345068724781056)), (23/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((60182191843/9903520314283042199192993792), (726792411/154742504910672534362390528)), (13/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-63017670097/158456325028528675187087900672), (-34653781599/158456325028528675187087900672)), (7/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((61753075543/2535301200456458802993406410752), (22370055849/2535301200456458802993406410752)), (7/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-114291932449/81129638414606681695789005144064), (-22255842795/81129638414606681695789005144064)), (55/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5282911233/18446744073709551616), (-61896026167/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-6682527311/147573952589676412928), (76135256849/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 2 => ⟨((119140435/147573952589676412928), (-25690174553/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 3 => ⟨((13792233277/18889465931478580854784), (25070578123/4722366482869645213696)), (17/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((-23669561143/151115727451828646838272), (-78771273691/151115727451828646838272)), (1/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((25218828163/1208925819614629174706176), (52592299677/1208925819614629174706176)), (7/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-5288963447/2417851639229258349412352), (-480749287/151115727451828646838272)), (21/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((30324984533/154742504910672534362390528), (16030580371/77371252455336267181195264)), (27/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-77377103797/4951760157141521099596496896), (-14951158169/1237940039285380274899124224)), (33/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((22506310749/19807040628566084398385987584), (12376350571/19807040628566084398385987584)), (21/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-48520273641/633825300114114700748351602688), (-17576472453/633825300114114700748351602688)), (45/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((12245564191/2535301200456458802993406410752), (9538218341/10141204801825835211973625643008)), (49/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-23329580501/81129638414606681695789005144064), (-108230217/10141204801825835211973625643008)), (25/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13365054621/1180591620717411303424), (-4758453553/73786976294838206464)), (3/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-1906246961/4722366482869645213696), (102760698213/4722366482869645213696)), (1/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-5172087479/9444732965739290427392), (-75211734369/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((23669561143/151115727451828646838272), (78771273691/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-7880883801/302231454903657293676544), (-16435093649/302231454903657293676544)), (17/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((31733780681/9671406556917033397649408), (1442247861/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-13267180733/38685626227668133590597632), (-28053515649/77371252455336267181195264)), (25/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((77377103797/2475880078570760549798248448), (14951158169/618970019642690137449562112)), (17/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-3164949949/1237940039285380274899124224), (-1740424299/1237940039285380274899124224)), (23/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((60650342051/316912650057057350374175801344), (10985295283/158456325028528675187087900672)), (29/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-33675301525/2535301200456458802993406410752), (-13115050219/5070602400912917605986812821504)), (35/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((69988741503/81129638414606681695789005144064), (324690651/10141204801825835211973625643008)), (39/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-34249289161/649037107316853453566312041152512), (4064736987/649037107316853453566312041152512)), (43/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((847220871/9444732965739290427392), (-91342842855/18889465931478580854784)), (17/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((9194822185/37778931862957161709568), (66854874995/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-31559414857/302231454903657293676544), (-105028364921/302231454903657293676544)), (3/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((14010460091/604462909807314587353088), (29217944265/604462909807314587353088)), (1/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-35259756313/9671406556917033397649408), (-51279923947/9671406556917033397649408)), (17/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((35379148621/77371252455336267181195264), (9351171883/19342813113834066795298816)), (17/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((-60182191841/1237940039285380274899124224), (-46514714303/1237940039285380274899124224)), (29/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((45012621497/9903520314283042199192993792), (12376350571/4951760157141521099596496896)), (21/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-30325171025/79228162514264337593543950336), (-10985295283/79228162514264337593543950336)), (15/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((74834003389/2535301200456458802993406410752), (14572278021/2535301200456458802993406410752)), (5/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-42770897585/20282409603651670423947251286016), (-396844129/5070602400912917605986812821504)), (49/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((91331437763/649037107316853453566312041152512), (-1354912329/81129638414606681695789005144064)), (59/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-91581266111/10384593717069655257060992658440192), (6419194559/2596148429267413814265248164610048)), (67/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-14711715497/302231454903657293676544), (-13370974999/37778931862957161709568)), (3/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((12623765943/302231454903657293676544), (84022691937/604462909807314587353088)), (5/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-16812552109/1208925819614629174706176), (-70123066235/2417851639229258349412352)), (21/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((28207805051/9671406556917033397649408), (20511969579/4835703278458516698824704)), (15/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((-17689574311/38685626227668133590597632), (-9351171883/19342813113834066795298816)), (17/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((36109315105/618970019642690137449562112), (13954414291/309485009821345068724781056)), (35/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-63017670095/9903520314283042199192993792), (-17326890799/4951760157141521099596496896)), (31/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((6065034205/9903520314283042199192993792), (17576472453/79228162514264337593543950336)), (49/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((-67350603049/1267650600228229401496703205376), (-13115050219/1267650600228229401496703205376)), (37/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((42770897585/10141204801825835211973625643008), (396844129/2535301200456458802993406410752)), (13/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((-100464581539/324518553658426726783156020576256), (11923228495/324518553658426726783156020576256)), (67/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((27474379833/1298074214633706907132624082305024), (-7703033471/1298074214633706907132624082305024)), (21/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((-56234695385/41538374868278621028243970633760768), (25693690361/41538374868278621028243970633760768)), (25/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/900814323), (-285760/300271441)), 0, by norm_num⟩
  | 1 => ⟨((-58555875123200/270488814840649443), (6262030336000/90162938280216481)), 0, by norm_num⟩
  | 2 => ⟨((16894726557/2251799813685248), (-33960840063/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-72704420725/288230376151711744), (1625097013/9007199254740992)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((9424077787/1152921504606846976), (-37003516751/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-37255484959/147573952589676412928), (50095763275/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 6 => ⟨((2146782289/295147905179352825856), (-65302623125/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-1760970411/9444732965739290427392), (82528034889/151115727451828646838272)), (11/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((4455018207/1208925819614629174706176), (-101513675797/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-282406957/19342813113834066795298816), (30447614285/38685626227668133590597632)), (23/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((-9807810331/2475880078570760549798248448), (-71311866661/2475880078570760549798248448)), (17/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((24482455163/79228162514264337593543950336), (81476549757/79228162514264337593543950336)), (3/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-43474882221/2535301200456458802993406410752), (-90664166447/2535301200456458802993406410752)), (33/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44604819523/2147483648), (11505775553/2147483648)), (7/4294967296), by norm_num⟩
  | 1 => ⟨((22063768773/17179869184), (5534451863/68719476736)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((83163875115/8796093022208), (-3376506445/2199023255552)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-32649930223/281474976710656), (5443306781/140737488355328)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((37344724051/18014398509481984), (-39125221079/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-49568157581/1152921504606846976), (37143763313/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((17541166163/18446744073709551616), (-9093740139/9223372036854775808)), (37/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-25189168059/1180591620717411303424), (36267610335/1180591620717411303424)), (47/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((17501467777/37778931862957161709568), (-73033834693/75557863725914323419136)), (59/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-1361812337/151115727451828646838272), (36920305891/1208925819614629174706176)), (37/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((2384108279/19342813113834066795298816), (-9329711437/9671406556917033397649408)), (195/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((2454077071/2475880078570760549798248448), (75139759835/2475880078570760549798248448)), (257/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-14612156823/79228162514264337593543950336), (-75065568399/79228162514264337593543950336)), (335/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-72084166643/72057594037927936), (36224896067/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 1 => ⟨((14540884145/144115188075855872), (-41602483533/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-15078524459/2305843009213693952), (29602813401/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 3 => ⟨((49673979945/147573952589676412928), (-33397175517/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-2146782289/147573952589676412928), (65302623127/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((4930717151/9444732965739290427392), (-57769624423/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-8316033987/604462909807314587353088), (23686524353/302231454903657293676544)), (3/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((677776697/9671406556917033397649408), (-73074274285/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((1838964437/77371252455336267181195264), (106967799993/618970019642690137449562112)), (19/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-22442250565/9903520314283042199192993792), (-37343418639/4951760157141521099596496896)), (1/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((11955592611/79228162514264337593543950336), (24932645773/79228162514264337593543950336)), (15/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-43764836927/5070602400912917605986812821504), (-31824631589/2535301200456458802993406410752)), (11/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((18297095045/40564819207303340847894502572032), (19344646481/40564819207303340847894502572032)), (9/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89209634749/4294967296), (23011553265/4294967296)), (1/536870912), by norm_num⟩
  | 1 => ⟨((44127541013/34359738368), (691805863/8589934592)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((83163817595/8796093022208), (-13505969317/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-65299670955/562949953421312), (5443243081/140737488355328)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((74688923985/36028797018963968), (-305658005/281474976710656)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-49567555687/1152921504606846976), (9285500081/288230376151711744)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((8770456189/9223372036854775808), (-36372069135/36893488147419103232)), (19/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-50378170645/2361183241434822606848), (72526300471/2361183241434822606848)), (95/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((17502365709/37778931862957161709568), (-18255194275/18889465931478580854784)), (119/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-21794476457/2417851639229258349412352), (73822377691/2417851639229258349412352)), (149/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((9548108499/77371252455336267181195264), (-74613343209/77371252455336267181195264)), (49/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((1216353761/1237940039285380274899124224), (75108681093/2475880078570760549798248448)), (129/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-14576420309/79228162514264337593543950336), (-37513892943/39614081257132168796771975168)), (21/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2872099897/2305843009213693952), (-1409657781/1152921504606846976)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-56770262795/295147905179352825856), (38168200591/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 2 => ⟨((19627723785/1180591620717411303424), (-37315784643/1180591620717411303424)), (7/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-18783684385/18889465931478580854784), (55018689927/18889465931478580854784)), (7/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((1485006069/37778931862957161709568), (-67675783865/302231454903657293676544)), (9/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((-677776697/2417851639229258349412352), (18268568571/1208925819614629174706176)), (3/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-9807810331/77371252455336267181195264), (-35655933331/38685626227668133590597632)), (3/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((9618107385/618970019642690137449562112), (8002161137/154742504910672534362390528)), (7/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-1601195439/1237940039285380274899124224), (-53427098085/19807040628566084398385987584)), (7/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((7163886997/79228162514264337593543950336), (10418778199/79228162514264337593543950336)), (15/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-57505155855/10141204801825835211973625643008), (-60797460369/10141204801825835211973625643008)), (13/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((26678166427/81129638414606681695789005144064), (41239019435/162259276829213363391578010288128)), (3/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-46558509509/2596148429267413814265248164610048), (-6400698477/649037107316853453566312041152512)), (11/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44604817377/2147483648), (5752888315/1073741824)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((88255082013/68719476736), (2767223461/34359738368)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((83163817741/8796093022208), (-13505969595/8796093022208)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-65299671515/562949953421312), (5443243491/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((74688925401/36028797018963968), (-9781058177/9007199254740992)), (19/36028797018963968), by norm_num⟩
  | 5 => ⟨((-24783778005/576460752303423488), (18571008873/576460752303423488)), (27/1152921504606846976), by norm_num⟩
  | 6 => ⟨((35081820079/36893488147419103232), (-36372103139/36893488147419103232)), (39/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-50378133955/2361183241434822606848), (36263211287/1180591620717411303424)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((35004633689/75557863725914323419136), (-18255245227/18889465931478580854784)), (15/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-21794257833/2417851639229258349412352), (73822695647/2417851639229258349412352)), (75/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((9547669769/77371252455336267181195264), (-74613807057/77371252455336267181195264)), (197/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((2433521675/2475880078570760549798248448), (37554655175/1237940039285380274899124224)), (259/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-7288920581/39614081257132168796771975168), (-75028567221/79228162514264337593543950336)), (337/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3925544757/1180591620717411303424), (59705255429/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((22540421261/37778931862957161709568), (-66022427913/37778931862957161709568)), (9/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-7128029131/151115727451828646838272), (40605470319/151115727451828646838272)), (3/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((1355553395/2417851639229258349412352), (-18268568571/604462909807314587353088)), (11/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((1838964437/4835703278458516698824704), (13370974999/4835703278458516698824704)), (19/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-20198025509/309485009821345068724781056), (-33609076775/154742504910672534362390528)), (1/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((35866777833/4951760157141521099596496896), (37398968659/2475880078570760549798248448)), (5/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-25789993189/39614081257132168796771975168), (-9376900379/9903520314283042199192993792)), (3/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((64693300337/1267650600228229401496703205376), (17099285729/316912650057057350374175801344)), (29/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((-73364957675/20282409603651670423947251286016), (-56703651723/20282409603651670423947251286016)), (1/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((38410770345/162259276829213363391578010288128), (42244609949/324518553658426726783156020576256)), (35/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-37639969855/2596148429267413814265248164610048), (-27270163321/5192296858534827628530496329220096)), (35/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((4353978379/5192296858534827628530496329220096), (13565466085/83076749736557242056487941267521536)), (35/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44604817377/2147483648), (5752888315/1073741824)), (5/2147483648), by norm_num⟩
  | 1 => ⟨((88255082013/68719476736), (2767223461/34359738368)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((83163817741/8796093022208), (-13505969593/8796093022208)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-65299671515/562949953421312), (21772973947/562949953421312)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((74688925415/36028797018963968), (-1222632269/1125899906842624)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-49567556085/1152921504606846976), (4642752187/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((17540910173/18446744073709551616), (-18186051291/18446744073709551616)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-12594533873/590295810358705651712), (36263210169/1180591620717411303424)), (97/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((35004637545/75557863725914323419136), (-73020976831/75557863725914323419136)), (121/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-21794266579/2417851639229258349412352), (73822688887/2417851639229258349412352)), (151/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((9547688085/77371252455336267181195264), (-74613796985/77371252455336267181195264)), (99/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((2433485779/2475880078570760549798248448), (75109297347/2475880078570760549798248448)), (65/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-7288887363/39614081257132168796771975168), (-18757138571/19807040628566084398385987584)), (169/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11520047081/1208925819614629174706176), (-8203125317/151115727451828646838272)), (11/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((-102693439/302231454903657293676544), (88574877921/4835703278458516698824704)), (15/4835703278458516698824704), by norm_num⟩
  | 2 => ⟨((-4458095605/9671406556917033397649408), (-16207242423/4835703278458516698824704)), (13/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((1275127873/9671406556917033397649408), (33948562399/77371252455336267181195264)), (1/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((-6792950347/309485009821345068724781056), (-56665104029/1237940039285380274899124224)), (15/1237940039285380274899124224), by norm_num⟩
  | 5 => ⟨((54706046157/19807040628566084398385987584), (19890394743/4951760157141521099596496896)), (7/4951760157141521099596496896), by norm_num⟩
  | 6 => ⟨((-45742737611/158456325028528675187087900672), (-48361616203/158456325028528675187087900672)), (11/79228162514264337593543950336), by norm_num⟩
  | 7 => ⟨((66695416067/2535301200456458802993406410752), (51548774293/2535301200456458802993406410752)), (15/1267650600228229401496703205376), by norm_num⟩
  | 8 => ⟨((-87297205327/40564819207303340847894502572032), (-48005238577/40564819207303340847894502572032)), (41/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((52277735909/324518553658426726783156020576256), (18937613417/324518553658426726783156020576256)), (13/162259276829213363391578010288128), by norm_num⟩
  | 10 => ⟨((-58053045053/5192296858534827628530496329220096), (-11304555071/5192296858534827628530496329220096)), (31/5192296858534827628530496329220096), by norm_num⟩
  | 11 => ⟨((60326996043/83076749736557242056487941267521536), (2238944287/83076749736557242056487941267521536)), (17/41538374868278621028243970633760768), by norm_num⟩
  | 12 => ⟨((-118085091249/2658455991569831745807614120560689152), (3503611679/664613997892457936451903530140172288)), (75/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44604817377/2147483648), (5752888315/1073741824)), (11/4294967296), by norm_num⟩
  | 1 => ⟨((88255082013/68719476736), (2767223461/34359738368)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((83163817741/8796093022208), (-13505969593/8796093022208)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((-65299671515/562949953421312), (21772973947/562949953421312)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((37344462707/18014398509481984), (-19562116305/18014398509481984)), (21/36028797018963968), by norm_num⟩
  | 5 => ⟨((-24783778041/576460752303423488), (37142017501/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 6 => ⟨((35081820335/36893488147419103232), (-36372102593/36893488147419103232)), (41/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-25189067715/1180591620717411303424), (36263210193/1180591620717411303424)), (49/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((17502318691/37778931862957161709568), (-9127622115/9444732965739290427392)), (61/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-10897133095/1208925819614629174706176), (18455672257/604462909807314587353088)), (19/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((2386921805/19342813113834066795298816), (-74613797153/77371252455336267181195264)), (199/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((2433487577/2475880078570760549798248448), (37554648707/1237940039285380274899124224)), (261/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-14577778245/79228162514264337593543950336), (-37514276933/39614081257132168796771975168)), (339/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((902723535/9671406556917033397649408), (52509090763/77371252455336267181195264)), (3/19342813113834066795298816), by norm_num⟩
  | 1 => ⟨((-6196841215/77371252455336267181195264), (-41245638009/154742504910672534362390528)), (21/309485009821345068724781056), by norm_num⟩
  | 2 => ⟨((33012245731/1237940039285380274899124224), (68844987927/1237940039285380274899124224)), (11/618970019642690137449562112), by norm_num⟩
  | 3 => ⟨((-55387366881/9903520314283042199192993792), (-80552455781/9903520314283042199192993792)), (15/4951760157141521099596496896), by norm_num⟩
  | 4 => ⟨((34734320539/39614081257132168796771975168), (18361470767/19807040628566084398385987584)), (9/19807040628566084398385987584), by norm_num⟩
  | 5 => ⟨((-1107849339/9903520314283042199192993792), (-13700078091/158456325028528675187087900672)), (35/633825300114114700748351602688), by norm_num⟩
  | 6 => ⟨((1933409259/158456325028528675187087900672), (8505543553/1267650600228229401496703205376)), (31/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((-372155723/316912650057057350374175801344), (-34512239661/81129638414606681695789005144064)), (49/81129638414606681695789005144064), by norm_num⟩
  | 8 => ⟨((16530764065/162259276829213363391578010288128), (3219003113/162259276829213363391578010288128)), (37/649037107316853453566312041152512), by norm_num⟩
  | 9 => ⟨((-2624459117/324518553658426726783156020576256), (-1558444645/5192296858534827628530496329220096)), (13/2596148429267413814265248164610048), by norm_num⟩
  | 10 => ⟨((12329186519/20769187434139310514121985316880384), (-5852956565/83076749736557242056487941267521536)), (67/166153499473114484112975882535043072), by norm_num⟩
  | 11 => ⟨((-53947251581/1329227995784915872903807060280344576), (3781318151/332306998946228968225951765070086144)), (21/664613997892457936451903530140172288), by norm_num⟩
  | 12 => ⟨((55209749555/21267647932558653966460912964485513216), (-25225391553/21267647932558653966460912964485513216)), (25/10633823966279326983230456482242756608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44604817377/2147483648), (5752888315/1073741824)), (3/1073741824), by norm_num⟩
  | 1 => ⟨((88255082013/68719476736), (2767223461/34359738368)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((83163817741/8796093022208), (-13505969593/8796093022208)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-65299671515/562949953421312), (21772973947/562949953421312)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((37344462707/18014398509481984), (-19562116305/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-24783778041/576460752303423488), (37142017501/1152921504606846976)), (15/576460752303423488), by norm_num⟩
  | 6 => ⟨((35081820335/36893488147419103232), (-36372102593/36893488147419103232)), (21/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-50378135433/2361183241434822606848), (72526420385/2361183241434822606848)), (99/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((17502318695/37778931862957161709568), (-73020976919/75557863725914323419136)), (123/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-10897133105/1208925819614629174706176), (73822689027/2417851639229258349412352)), (153/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((4773843633/38685626227668133590597632), (-37306898579/38685626227668133590597632)), (25/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((2433487477/2475880078570760549798248448), (37554648721/1237940039285380274899124224)), (131/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-14577778039/79228162514264337593543950336), (-9378569245/9903520314283042199192993792)), (85/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((330703068219395/524288), (-878384378096323/1048576)), (6141513/1048576), by norm_num⟩
  | 1 => ⟨((56162918345/64), (-16400518315/16)), (131/16), by norm_num⟩
  | 2 => ⟨((4875689427/8), (-40433009335/64)), (369/64), by norm_num⟩
  | 3 => ⟨((36135387753/128), (-8362593685/32)), (351/128), by norm_num⟩
  | 4 => ⟨((25152548989/256), (-41760664913/512)), (505/512), by norm_num⟩
  | 5 => ⟨((28088719321/1024), (-41929877657/2048)), (587/2048), by norm_num⟩
  | 6 => ⟨((26227342695/4096), (-17621350553/4096)), (575/8192), by norm_num⟩
  | 7 => ⟨((84281118007/65536), (-25484890587/32768)), (487/32768), by norm_num⟩
  | 8 => ⟨((59486909313/262144), (-16170580425/131072)), (729/262144), by norm_num⟩
  | 9 => ⟨((74961957793/2097152), (-36546908567/2097152)), (245/524288), by norm_num⟩
  | 10 => ⟨((42694990201/8388608), (-37191382583/16777216)), (599/8388608), by norm_num⟩
  | 11 => ⟨((88820815743/134217728), (-8594288885/33554432)), (673/67108864), by norm_num⟩
  | 12 => ⟨((21267802363/268435456), (-29051011481/1073741824)), (175/134217728), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1611031970695751/10141204801825835211973625643008), (-1205424511999/10141204801825835211973625643008)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((56707803010961/19807040628566084398385987584), (-1480343082855/633825300114114700748351602688)), (4477/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1930152910205713/39614081257132168796771975168), (-417482299135/9903520314283042199192993792)), (5051/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((966247798559627/1237940039285380274899124224), (-1778155198359/2475880078570760549798248448)), (5379/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((907104445531367/77371252455336267181195264), (-445616884091/38685626227668133590597632)), (337/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((794966540204703/4835703278458516698824704), (-418914777265/2417851639229258349412352)), (2535/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((80885693298241/37778931862957161709568), (-183851772723/75557863725914323419136)), (4451/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((972691432737683/37778931862957161709568), (-599689254707/18889465931478580854784)), (1815/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((670407717101009/2361183241434822606848), (-903351011029/2361183241434822606848)), (5469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((52533991738657/18446744073709551616), (-1248344203421/295147905179352825856)), (7559/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1898227728595153/73786976294838206464), (-1569844494189/36893488147419103232)), (9509/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1907035468028253/9223372036854775808), (-3558233701881/9223372036854775808)), (2695/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1678637755770843/1152921504606846976), (-448891537167/144115188075855872)), (2721/288230376151711744), by norm_num⟩
  | 5 => ⟨((1269052126425419/144115188075855872), (-3179660116589/144115188075855872)), (4821/72057594037927936), by norm_num⟩
  | 4 => ⟨((1604153802054327/36028797018963968), (-4845362220669/36028797018963968)), (14703/36028797018963968), by norm_num⟩
  | 3 => ⟨((815668243293755/4503599627370496), (-6191837938509/9007199254740992)), (2351/1125899906842624), by norm_num⟩
  | 2 => ⟨((314559284065057/562949953421312), (-3199672664521/1125899906842624)), (19467/2251799813685248), by norm_num⟩
  | 1 => ⟨((1330029518908549/1125899906842624), (-10134999004157/1125899906842624)), (30905/1125899906842624), by norm_num⟩
  | 0 => ⟨((778702407182559/562949953421312), (-22520439747231/1125899906842624)), (8623/140737488355328), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((778702407182559/562949953421312), (-22520439747231/1125899906842624)), (32894135058355287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1076917482124013/562949953421312), (-15575736826515/281474976710656)), (193605/1125899906842624), by norm_num⟩
  | 2 => ⟨((1029204143237877/281474976710656), (-119184898646813/562949953421312)), (190539/281474976710656), by norm_num⟩
  | 3 => ⟨((1875317516282937/140737488355328), (-217897862417769/140737488355328)), (737041/140737488355328), by norm_num⟩
  | 4 => ⟨((1540694819915421/8796093022208), (-181467142713677/4398046511104)), (685135/4398046511104), by norm_num⟩
  | 5 => ⟨((995656549463119/34359738368), (-248321795804975/17179869184)), (1158401/17179869184), by norm_num⟩
  | 6 => ⟨((330703068219395/524288), (-878384378096323/1048576)), (6141513/1048576), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((44604817377/2147483648), (5752888315/1073741824)), (3/1073741824), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/10274641), (-3429120/10274641)), 0, by norm_num⟩
  | 1 => ⟨((3341878067200/105568247678881), (7725121536000/105568247678881)), 0, by norm_num⟩
  | 2 => ⟨((-34484249897/2199023255552), (-12049490313/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((38286765359/17592186044416), (-40752016589/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((20824525207/140737488355328), (21713270157/35184372088832)), (5/140737488355328), by norm_num⟩
  | 5 => ⟨((-33552814763/281474976710656), (-24186309607/562949953421312)), (7/562949953421312), by norm_num⟩
  | 6 => ⟨((45571094931/2251799813685248), (-34186369731/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 7 => ⟨((1417723647/4503599627370496), (5676203353/1125899906842624)), (21/18014398509481984), by norm_num⟩
  | 8 => ⟨((-7888487549/9007199254740992), (-36040468289/72057594037927936)), (3/9007199254740992), by norm_num⟩
  | 9 => ⟨((51730579905/288230376151711744), (-26319673151/288230376151711744)), (27/288230376151711744), by norm_num⟩
  | 10 => ⟨((-10233090505/2305843009213693952), (46071356817/1152921504606846976)), (61/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-7127142347/1152921504606846976), (-5904576145/1152921504606846976)), (17/2305843009213693952), by norm_num⟩
  | 12 => ⟨((56533013939/36893488147419103232), (-8672222981/18446744073709551616)), (19/9223372036854775808), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (2679/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (2679/1280)))⁻¹=value ((2252800/10274641), (-3429120/10274641)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/10274641), (-3429120/10274641))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((204800/864139), (-180480/864139)), 0, by norm_num⟩
  | 1 => ⟨((-246579200/39301905859), (36962304000/746736211321)), 0, by norm_num⟩
  | 2 => ⟨((-2855733821440000/645283882914717619), (-4207714762752000/645283882914717619)), 0, by norm_num⟩
  | 3 => ⟨((84820242931/70368744177664), (21853170359/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-12333227605/70368744177664), (6267989383/70368744177664)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((25821740061/2251799813685248), (-64981863219/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 6 => ⟨((14904163125/9007199254740992), (41587275273/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 7 => ⟨((-48871971057/72057594037927936), (-13486651141/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 8 => ⟨((68864482535/576460752303423488), (-15258105601/576460752303423488)), (9/288230376151711744), by norm_num⟩
  | 9 => ⟨((-52536284669/4611686018427387904), (71995462929/4611686018427387904)), (33/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-5171182065/18446744073709551616), (-112141308123/36893488147419103232)), (15/9223372036854775808), by norm_num⟩
  | 11 => ⟨((12936217127/36893488147419103232), (48834620415/147573952589676412928)), (27/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-44925692193/590295810358705651712), (-1533124631/590295810358705651712)), (97/1180591620717411303424), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (2679/1280)))⁻¹=value ((204800/864139), (-180480/864139)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((204800/864139), (-180480/864139))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-157514137600/8878717999099), (-1108869120000/8878717999099)), 0, by norm_num⟩
  | 1 => ⟨((83409098877/2199023255552), (52068665425/2199023255552)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-99009481011/8796093022208), (33257868729/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((34163409253/35184372088832), (-92430618357/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((45490980417/140737488355328), (37158550931/70368744177664)), (3/70368744177664), by norm_num⟩
  | 5 => ⟨((-73561064541/562949953421312), (-3970421901/281474976710656)), (7/562949953421312), by norm_num⟩
  | 6 => ⟨((20922527075/1125899906842624), (-44583188549/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 7 => ⟨((17888887353/18014398509481984), (48781289609/9007199254740992)), (23/18014398509481984), by norm_num⟩
  | 8 => ⟨((-71715960709/72057594037927936), (-1066662659/2251799813685248)), (27/72057594037927936), by norm_num⟩
  | 9 => ⟨((55014097697/288230376151711744), (-1926211849/18014398509481984)), (15/144115188075855872), by norm_num⟩
  | 10 => ⟨((-4793346373/1152921504606846976), (6196971587/144115188075855872)), (33/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-30125596529/4611686018427387904), (-6286096617/1152921504606846976)), (37/4611686018427387904), by norm_num⟩
  | 12 => ⟨((29670434851/18446744073709551616), (-17248625673/36893488147419103232)), (81/36893488147419103232), by norm_num⟩
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
  | 0 => ⟨((27/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/2871049), (-1143040/8613147)), 0, by norm_num⟩
  | 1 => ⟨((-1045422899200/74186301243609), (234094592000/8242922360401)), 0, by norm_num⟩
  | 2 => ⟨((-828176227/2199023255552), (-69907427441/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((42780619551/140737488355328), (56323321463/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-8314791755/140737488355328), (-796967513/35184372088832)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((70477142525/9007199254740992), (-6739942997/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-53172398063/72057594037927936), (48950433033/72057594037927936)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((9765318329/288230376151711744), (-17531758839/144115188075855872)), (9/288230376151711744), by norm_num⟩
  | 8 => ⟨((10253891407/2305843009213693952), (70395849737/4611686018427387904)), (13/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-3432694733/2305843009213693952), (-49372158245/36893488147419103232)), (37/36893488147419103232), by norm_num⟩
  | 10 => ⟨((18305578515/73786976294838206464), (13107146029/295147905179352825856)), (13/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-34817787615/1180591620717411303424), (27649332957/2361183241434822606848)), (73/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((44930383155/18889465931478580854784), (-7579082211/2361183241434822606848)), (51/9444732965739290427392), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (2679/1280)))⁻¹=value ((614400/2871049), (-1143040/8613147)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/2871049), (-1143040/8613147))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-22397662637/1099511627776), (-53594753093/2199023255552)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((16554347873/1099511627776), (5671452695/4398046511104)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-63394667341/17592186044416), (55661004365/17592186044416)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((612110669/17592186044416), (-44638186585/35184372088832)), (5/70368744177664), by norm_num⟩
  | 4 => ⟨((61842643871/281474976710656), (14648313261/70368744177664)), (7/281474976710656), by norm_num⟩
  | 5 => ⟨((-18902919537/281474976710656), (932766141/140737488355328)), (5/562949953421312), by norm_num⟩
  | 6 => ⟨((36457375929/4503599627370496), (-53450306335/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 7 => ⟨((30717212513/36028797018963968), (102114434933/36028797018963968)), (15/18014398509481984), by norm_num⟩
  | 8 => ⟨((-80003586919/144115188075855872), (-1945375421/9007199254740992)), (35/144115188075855872), by norm_num⟩
  | 9 => ⟨((57868528647/576460752303423488), (-8926206501/144115188075855872)), (39/576460752303423488), by norm_num⟩
  | 10 => ⟨((-8368245659/4611686018427387904), (13282847091/576460752303423488)), (85/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-31878630653/9223372036854775808), (-53232931505/18446744073709551616)), (95/18446744073709551616), by norm_num⟩
  | 12 => ⟨((62236480119/73786976294838206464), (-134931473/576460752303423488)), (13/9223372036854775808), by norm_num⟩
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
  | 0 => ⟨((35/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/38537041), (-3429120/38537041)), 0, by norm_num⟩
  | 1 => ⟨((-19810680012800/1485103529035681), (24579932160000/1485103529035681)), 0, by norm_num⟩
  | 2 => ⟨((17740937039/35184372088832), (-9379980125/4398046511104)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((105542599/2199023255552), (62145028967/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-32170453199/2251799813685248), (-41428197177/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((77361428561/36028797018963968), (38745262853/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-71348381489/288230376151711744), (-645842125/144115188075855872)), (9/288230376151711744), by norm_num⟩
  | 7 => ⟨((53543762097/2305843009213693952), (-24433984875/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-31140389891/18446744073709551616), (37236983407/18446744073709551616)), (25/36893488147419103232), by norm_num⟩
  | 9 => ⟨((9915056031/147573952589676412928), (-77577067911/295147905179352825856)), (29/295147905179352825856), by norm_num⟩
  | 10 => ⟨((6429078551/1180591620717411303424), (32388177217/1180591620717411303424)), (33/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-32622448893/18889465931478580854784), (-21808874475/9444732965739290427392)), (37/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((19898165453/75557863725914323419136), (41681608617/302231454903657293676544)), (41/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (2679/1280)))⁻¹=value ((7168000/38537041), (-3429120/38537041)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/38537041), (-3429120/38537041))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-52404203145/8796093022208), (-23931120645/8796093022208)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((63161918137/17592186044416), (-19560911869/17592186044416)), (3/17592186044416), by norm_num⟩
  | 2 => ⟨((-11842597613/17592186044416), (41246924353/35184372088832)), (5/70368744177664), by norm_num⟩
  | 3 => ⟨((-27013400797/281474976710656), (-53206284159/140737488355328)), (9/281474976710656), by norm_num⟩
  | 4 => ⟨((374427963/4398046511104), (28180530999/562949953421312)), (7/562949953421312), by norm_num⟩
  | 5 => ⟨((-99288323559/4503599627370496), (28556285935/4503599627370496)), (17/4503599627370496), by norm_num⟩
  | 6 => ⟨((9988489833/4503599627370496), (-81036842407/18014398509481984)), (21/18014398509481984), by norm_num⟩
  | 7 => ⟨((29158372951/72057594037927936), (69777140867/72057594037927936)), (13/36028797018963968), by norm_num⟩
  | 8 => ⟨((-29283045625/144115188075855872), (-18109553465/288230376151711744)), (31/288230376151711744), by norm_num⟩
  | 9 => ⟨((40183004941/1152921504606846976), (-27266815703/1152921504606846976)), (69/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-2196768679/4611686018427387904), (37804383161/4611686018427387904)), (77/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-11253235765/9223372036854775808), (-37365191425/36893488147419103232)), (85/36893488147419103232), by norm_num⟩
  | 12 => ⟨((21736709763/73786976294838206464), (-5805780887/73786976294838206464)), (185/295147905179352825856), by norm_num⟩
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
  | 0 => ⟨((43/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/54511441), (-3429120/54511441)), 0, by norm_num⟩
  | 1 => ⟨((-32896908492800/2971497199896481), (30198202368000/2971497199896481)), 0, by norm_num⟩
  | 2 => ⟨((2527144355/4398046511104), (-82268505139/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-5428007557/562949953421312), (31668341465/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-24859057447/9007199254740992), (-84588694521/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((37348753093/72057594037927936), (3025407035/4503599627370496)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-72630595047/1152921504606846976), (-43765308791/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((115893552387/18446744073709551616), (20011327787/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-79926430423/147573952589676412928), (1014397791/9223372036854775808)), (9/73786976294838206464), by norm_num⟩
  | 9 => ⟨((5945616525/147573952589676412928), (-30599697733/1180591620717411303424)), (17/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-23037056271/9444732965739290427392), (31742256707/9444732965739290427392)), (1/590295810358705651712), by norm_num⟩
  | 11 => ⟨((6899507575/75557863725914323419136), (-105234962287/302231454903657293676544)), (29/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1080727437/302231454903657293676544), (74947798907/2417851639229258349412352)), (53/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (2679/1280)))⁻¹=value ((8806400/54511441), (-3429120/54511441)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/54511441), (-3429120/54511441))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-39885576241/35184372088832), (-4556360161/70368744177664)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((5310055229/8796093022208), (-7668637425/17592186044416)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-19719737407/281474976710656), (40241608221/140737488355328)), (7/281474976710656), by norm_num⟩
  | 3 => ⟨((-23993335083/562949953421312), (-45226242333/562949953421312)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((25751928681/1125899906842624), (8872432065/1125899906842624)), (9/2251799813685248), by norm_num⟩
  | 5 => ⟨((-23680581097/4503599627370496), (22464795543/9007199254740992)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((15189924973/36028797018963968), (-44427035197/36028797018963968)), (7/18014398509481984), by norm_num⟩
  | 7 => ⟨((9440799125/72057594037927936), (70284560759/288230376151711744)), (17/144115188075855872), by norm_num⟩
  | 8 => ⟨((-63446663337/1152921504606846976), (-3730951243/288230376151711744)), (41/1152921504606846976), by norm_num⟩
  | 9 => ⟨((41482854119/4611686018427387904), (-7722882335/1152921504606846976)), (47/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-2847369971/36893488147419103232), (80364770049/36893488147419103232)), (103/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-11920146959/36893488147419103232), (-19571751207/73786976294838206464)), (115/147573952589676412928), by norm_num⟩
  | 12 => ⟨((5687686103/73786976294838206464), (-5896970833/295147905179352825856)), (249/1180591620717411303424), by norm_num⟩
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
  | 0 => ⟨((51/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/24587547), (-1143040/24587547)), 0, by norm_num⟩
  | 1 => ⟨((-600833228800/67171940830801), (3979608064000/604547467477209)), 0, by norm_num⟩
  | 2 => ⟨((33796245495/70368744177664), (-47426786289/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-20645994337/1125899906842624), (66294229219/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-158448579/2251799813685248), (-82776597703/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((32221253733/288230376151711744), (93297992859/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-35599298255/2305843009213693952), (-46852353359/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((57751716603/36893488147419103232), (39834711963/36893488147419103232)), (5/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-80236079081/590295810358705651712), (-11823222711/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 9 => ⟨((24921458485/2361183241434822606848), (-1526884069/4722366482869645213696)), (25/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-27947124641/37778931862957161709568), (5066666259/18889465931478580854784)), (19/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((27889859773/604462909807314587353088), (-43745651793/1208925819614629174706176)), (29/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-2932371451/1208925819614629174706176), (35150039475/9671406556917033397649408)), (45/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (2679/1280)))⁻¹=value ((3481600/24587547), (-1143040/24587547)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/24587547), (-1143040/24587547))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-92059397841/562949953421312), (6126531825/140737488355328)), (7/562949953421312), by norm_num⟩
  | 1 => ⟨((42661946303/562949953421312), (-54421895165/562949953421312)), (7/562949953421312), by norm_num⟩
  | 2 => ⟨((17874299/70368744177664), (117884296579/2251799813685248)), (7/1125899906842624), by norm_num⟩
  | 3 => ⟨((-49560969183/4503599627370496), (-29487425531/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((10557760817/2251799813685248), (6520165293/9007199254740992)), (9/9007199254740992), by norm_num⟩
  | 5 => ⟨((-70428064219/72057594037927936), (47222186777/72057594037927936)), (25/72057594037927936), by norm_num⟩
  | 6 => ⟨((4059757525/72057594037927936), (-75897794143/288230376151711744)), (15/144115188075855872), by norm_num⟩
  | 7 => ⟨((18458336895/576460752303423488), (27895559743/576460752303423488)), (9/288230376151711744), by norm_num⟩
  | 8 => ⟨((-54353481533/4611686018427387904), (-18044649587/9223372036854775808)), (85/9223372036854775808), by norm_num⟩
  | 9 => ⟨((33983289333/18446744073709551616), (-13854700421/9223372036854775808)), (99/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-764049075/147573952589676412928), (34031044267/73786976294838206464)), (55/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-10099263331/147573952589676412928), (-8162683001/147573952589676412928)), (61/295147905179352825856), by norm_num⟩
  | 12 => ⟨((76110324691/4722366482869645213696), (-19301197873/4722366482869645213696)), (133/2361183241434822606848), by norm_num⟩
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
  | 0 => ⟨((59/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/96290641), (-3429120/96290641)), 0, by norm_num⟩
  | 1 => ⟨((-67122429132800/9271887544190881), (41434742784000/9271887544190881)), 0, by norm_num⟩
  | 2 => ⟨((26363531445/70368744177664), (-3600203173/8796093022208)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-36521363445/2251799813685248), (36424683291/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((15908978639/36028797018963968), (-41768944257/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((978600543/72057594037927936), (44197807815/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-33042977219/9223372036854775808), (-86509424585/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((14454490969/36893488147419103232), (38716217295/73786976294838206464)), (11/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-40051706841/1180591620717411303424), (-30630883737/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((97868661631/37778931862957161709568), (38679062969/37778931862957161709568)), (21/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-27317333169/151115727451828646838272), (-5473573229/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((28203411367/2417851639229258349412352), (-20140781407/9671406556917033397649408)), (37/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-53757443969/77371252455336267181195264), (26179766229/77371252455336267181195264)), (25/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (2679/1280)))⁻¹=value ((12083200/96290641), (-3429120/96290641)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/96290641), (-3429120/96290641))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-21359036643/1125899906842624), (50829044515/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 1 => ⟨((7944724711/1125899906842624), (-35749283103/2251799813685248)), (11/4503599627370496), by norm_num⟩
  | 2 => ⟨((15637960563/9007199254740992), (17298508127/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((-75408762151/36028797018963968), (-61336771641/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 4 => ⟨((6987526019/9007199254740992), (-237240325/36028797018963968)), (15/72057594037927936), by norm_num⟩
  | 5 => ⟨((-42620092745/288230376151711744), (37835963477/288230376151711744)), (21/288230376151711744), by norm_num⟩
  | 6 => ⟨((5341259591/1152921504606846976), (-105882628593/2305843009213693952)), (51/2305843009213693952), by norm_num⟩
  | 7 => ⟨((3613473205/576460752303423488), (36412747737/4611686018427387904)), (31/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-76832699945/36893488147419103232), (-7731681265/36893488147419103232)), (73/36893488147419103232), by norm_num⟩
  | 9 => ⟨((11513734897/36893488147419103232), (-5128871077/18446744073709551616)), (43/73786976294838206464), by norm_num⟩
  | 10 => ⟨((168920319/147573952589676412928), (95700640427/1180591620717411303424)), (191/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-57011845533/4722366482869645213696), (-5648866539/590295810358705651712)), (213/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((105962155349/37778931862957161709568), (-26497807941/37778931862957161709568)), (29/2361183241434822606848), by norm_num⟩
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
  | 0 => ⟨((67/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/122095441), (-3429120/122095441)), 0, by norm_num⟩
  | 1 => ⟨((-88261721292800/14907296712984481), (47053012992000/14907296712984481)), 0, by norm_num⟩
  | 2 => ⟨((40584842789/140737488355328), (-18331517959/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-7062786711/562949953421312), (42081558787/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((7972393389/18014398509481984), (-22091009597/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-8817042149/1152921504606846976), (43305438853/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((-11532955921/18446744073709551616), (-79850615559/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 7 => ⟨((28310177497/295147905179352825856), (69200311363/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-10250294329/1180591620717411303424), (-27927660183/2361183241434822606848)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((49412908109/75557863725914323419136), (20502859129/37778931862957161709568)), (9/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-53639197781/1208925819614629174706176), (-6441211383/302231454903657293676544)), (21/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((27007277475/9671406556917033397649408), (22225191331/38685626227668133590597632)), (3/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-102119788895/618970019642690137449562112), (2145193807/309485009821345068724781056)), (55/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (2679/1280)))⁻¹=value ((13721600/122095441), (-3429120/122095441)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/122095441), (-3429120/122095441))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2043527849/1125899906842624), (64895239857/36028797018963968)), (3/9007199254740992), by norm_num⟩
  | 1 => ⟨((1908775371/4503599627370496), (-75987606829/36028797018963968)), (7/18014398509481984), by norm_num⟩
  | 2 => ⟨((30024535057/72057594037927936), (33832803181/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-23032220461/72057594037927936), (-25862836727/144115188075855872)), (15/144115188075855872), by norm_num⟩
  | 4 => ⟨((1936199231/18014398509481984), (-9760849581/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 5 => ⟨((-43195456273/2305843009213693952), (24633799827/1152921504606846976)), (15/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-302704401/18446744073709551616), (-62298380687/9223372036854775808)), (73/18446744073709551616), by norm_num⟩
  | 7 => ⟨((37705002095/36893488147419103232), (40236818169/36893488147419103232)), (45/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-23071383243/73786976294838206464), (-3540296861/295147905179352825856)), (53/147573952589676412928), by norm_num⟩
  | 9 => ⟨((53129496421/1180591620717411303424), (-51625735035/1180591620717411303424)), (31/295147905179352825856), by norm_num⟩
  | 10 => ⟨((2316758337/4722366482869645213696), (57457328833/4722366482869645213696)), (139/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-17226977751/9444732965739290427392), (-53389214265/37778931862957161709568)), (311/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((15786081273/37778931862957161709568), (-3921549325/37778931862957161709568)), (341/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((75/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/50392347), (-1143040/50392347)), 0, by norm_num⟩
  | 1 => ⟨((-4151309926400/846462878722803), (5852364800000/2539388636168409)), 0, by norm_num⟩
  | 2 => ⟨((31385508803/140737488355328), (-6076351573/35184372088832)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-42200615411/4503599627370496), (50902514129/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((25064685501/72057594037927936), (-49032503095/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((-22951128647/2305843009213693952), (44402989043/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 6 => ⟨((635056489/9223372036854775808), (-76348206745/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((11789583421/590295810358705651712), (62518445257/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-1307973915/590295810358705651712), (-24338495231/4722366482869645213696)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((12921721649/75557863725914323419136), (71536299623/302231454903657293676544)), (21/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-27496692011/2417851639229258349412352), (-48767036029/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((6693651301/9671406556917033397649408), (7414919047/19342813113834066795298816)), (23/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-48908085755/1237940039285380274899124224), (-28781720405/2475880078570760549798248448)), (47/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (2679/1280)))⁻¹=value ((5120000/50392347), (-1143040/50392347)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/50392347), (-1143040/50392347))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-41376719019/288230376151711744), (32307311933/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 1 => ⟨((-3885793/144115188075855872), (-136574272187/576460752303423488)), (15/288230376151711744), by norm_num⟩
  | 2 => ⟨((38233099801/576460752303423488), (28244869541/288230376151711744)), (19/576460752303423488), by norm_num⟩
  | 3 => ⟨((-23650625537/576460752303423488), (-4383797135/288230376151711744)), (35/2305843009213693952), by norm_num⟩
  | 4 => ⟨((14749314905/1152921504606846976), (-17759556297/4611686018427387904)), (13/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-37352881463/18446744073709551616), (3385588823/1152921504606846976)), (9/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-3147480299/36893488147419103232), (-31656039041/36893488147419103232)), (23/36893488147419103232), by norm_num⟩
  | 7 => ⟨((42100283579/295147905179352825856), (38443106519/295147905179352825856)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-96252132879/2361183241434822606848), (2064843229/2361183241434822606848)), (131/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((53281967119/9444732965739290427392), (-56389659611/9444732965739290427392)), (155/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((8080852135/75557863725914323419136), (120316045737/75557863725914323419136)), (87/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-36399139399/151115727451828646838272), (-27487001761/151115727451828646838272)), (195/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((65765567397/1208925819614629174706176), (-16339930533/1208925819614629174706176)), (429/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((83/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/183535441), (-3429120/183535441)), 0, by norm_num⟩
  | 1 => ⟨((-138593369292800/33685258103064481), (58289553408000/33685258103064481)), 0, by norm_num⟩
  | 2 => ⟨((24539485083/140737488355328), (-33374008249/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-1960984983/281474976710656), (64127335057/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((4613687125/18014398509481984), (-56893407639/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-1177723685/144115188075855872), (95341934075/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((3418222121/18446744073709551616), (-76274930209/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((2540210079/2361183241434822606848), (117116366557/2361183241434822606848)), (15/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-9693726279/18889465931478580854784), (-86395527721/37778931862957161709568)), (15/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((27278276159/604462909807314587353088), (238731793/2361183241434822606848)), (15/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-3668277239/1208925819614629174706176), (-41205011571/9671406556917033397649408)), (15/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((27902433507/154742504910672534362390528), (52287454687/309485009821345068724781056)), (27/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-12290742343/1237940039285380274899124224), (-15200148383/2475880078570760549798248448)), (25/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (2679/1280)))⁻¹=value ((16998400/183535441), (-3429120/183535441)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/183535441), (-3429120/183535441))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1312462375/144115188075855872), (27029786733/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 1 => ⟨((-19490354541/4611686018427387904), (-106589016673/4611686018427387904)), (29/4611686018427387904), by norm_num⟩
  | 2 => ⟨((38669908051/4611686018427387904), (10223554503/1152921504606846976)), (19/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-42013490799/9223372036854775808), (-17974516243/18446744073709551616)), (9/4611686018427387904), by norm_num⟩
  | 4 => ⟨((49176529143/36893488147419103232), (-5470527057/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-27870682883/147573952589676412928), (51609836541/147573952589676412928)), (39/147573952589676412928), by norm_num⟩
  | 6 => ⟨((-2723330129/147573952589676412928), (-113140610759/1180591620717411303424)), (99/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((20535594149/1180591620717411303424), (32262626437/2361183241434822606848)), (61/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-88634221341/18889465931478580854784), (3516958821/9444732965739290427392)), (143/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((11801221873/18889465931478580854784), (-54359852197/75557863725914323419136)), (169/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((2636429921/151115727451828646838272), (111604425343/604462909807314587353088)), (381/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-34139630817/1208925819614629174706176), (-50129592095/2417851639229258349412352)), (107/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((7600779869/1208925819614629174706176), (-7601244241/4835703278458516698824704)), (59/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((91/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/219170641), (-3429120/219170641)), 0, by norm_num⟩
  | 1 => ⟨((-167785725132800/48035769876350881), (63907823616000/48035769876350881)), 0, by norm_num⟩
  | 2 => ⟨((38871686115/281474976710656), (-11806479661/140737488355328)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-11743765785/2251799813685248), (20928557729/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((53432834371/288230376151711744), (-68707437353/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-6937160895/1152921504606846976), (3339211773/288230376151711744)), (5/4611686018427387904), by norm_num⟩
  | 6 => ⟨((24378228263/147573952589676412928), (-79636139237/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-13231720153/4722366482869645213696), (114450268535/4722366482869645213696)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-5324318331/75557863725914323419136), (-39756418303/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((13574347821/1208925819614629174706176), (13355868287/302231454903657293676544)), (23/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-31842068169/38685626227668133590597632), (-34643126011/19342813113834066795298816)), (5/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((30333447027/618970019642690137449562112), (2696720107/38685626227668133590597632)), (17/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-52070946141/19807040628566084398385987584), (-51110108513/19807040628566084398385987584)), (7/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (2679/1280)))⁻¹=value ((18636800/219170641), (-3429120/219170641)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/219170641), (-3429120/219170641))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3759350525/9223372036854775808), (78806680275/36893488147419103232)), (21/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-13288616519/18446744073709551616), (-73537596071/36893488147419103232)), (25/36893488147419103232), by norm_num⟩
  | 2 => ⟨((16564851163/18446744073709551616), (25897416305/36893488147419103232)), (17/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-16463793341/36893488147419103232), (-5077638917/147573952589676412928)), (33/147573952589676412928), by norm_num⟩
  | 4 => ⟨((72787081323/590295810358705651712), (-43279080477/590295810358705651712)), (13/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-18011816087/1180591620717411303424), (86831813803/2361183241434822606848)), (73/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-12786454789/4722366482869645213696), (-45066602773/4722366482869645213696)), (95/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((35562328333/18889465931478580854784), (6017656597/4722366482869645213696)), (117/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-73016810391/151115727451828646838272), (9917427513/151115727451828646838272)), (69/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((18707606035/302231454903657293676544), (-2928695287/37778931862957161709568)), (163/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1418695053/604462909807314587353088), (46440335201/2417851639229258349412352)), (369/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-57559240085/19342813113834066795298816), (-5124487767/2417851639229258349412352)), (13/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((101066641325/154742504910672534362390528), (-25563563001/154742504910672534362390528)), (919/154742504910672534362390528), by norm_num⟩
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
  | 0 => ⟨((99/8), (2679/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/28675849), (-1143040/86027547)), 0, by norm_num⟩
  | 1 => ⟨((-22184715059200/7400738842837209), (2575040512000/2466912947612403)), 0, by norm_num⟩
  | 2 => ⟨((62382617165/562949953421312), (-34293107819/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-71122945935/18014398509481984), (56367501281/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((9677063305/72057594037927936), (-335830287/2251799813685248)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-39516797995/9223372036854775808), (15565411133/2305843009213693952)), (5/9223372036854775808), by norm_num⟩
  | 6 => ⟨((36435357601/295147905179352825856), (-21665542977/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-13687373123/4722366482869645213696), (29169479575/2361183241434822606848)), (7/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((1200591185/37778931862957161709568), (-76240367331/151115727451828646838272)), (11/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((5085765155/2417851639229258349412352), (48426552817/2417851639229258349412352)), (17/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-16687700679/77371252455336267181195264), (-7473717263/9671406556917033397649408)), (13/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((33686738693/2475880078570760549798248448), (71606506529/2475880078570760549798248448)), (5/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-28783111159/39614081257132168796771975168), (-20711511113/19807040628566084398385987584)), (15/39614081257132168796771975168), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (2679/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (2679/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (2679/1280)))⁻¹=value ((2252800/28675849), (-1143040/86027547)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/28675849), (-1143040/86027547))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2148072971/590295810358705651712), (6390922899/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 1 => ⟨((-24817618275/295147905179352825856), (-45407835205/295147905179352825856)), (5/73786976294838206464), by norm_num⟩
  | 2 => ⟨((49701746933/590295810358705651712), (14373425977/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 3 => ⟨((-11553855745/295147905179352825856), (2210866487/1180591620717411303424)), (27/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((24174037729/2361183241434822606848), (-18256379307/2361183241434822606848)), (11/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-20036828587/18889465931478580854784), (65423554241/18889465931478580854784)), (31/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-12121653109/37778931862957161709568), (-64741193579/75557863725914323419136)), (81/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((27673842233/151115727451828646838272), (32223954375/302231454903657293676544)), (101/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-108777168295/2417851639229258349412352), (2600507441/302231454903657293676544)), (239/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((13401641371/2417851639229258349412352), (-18253555129/2417851639229258349412352)), (141/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((164427101/604462909807314587353088), (8758068627/4835703278458516698824704)), (161/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-44048234513/154742504910672534362390528), (-30376140347/154742504910672534362390528)), (363/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((76258083191/1237940039285380274899124224), (-19604826479/1237940039285380274899124224)), (803/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39256704879/274877906944), (7718133211/68719476736)), (77/68719476736), by norm_num⟩
  | 1 => ⟨((-4148504495/549755813888), (17748841731/137438953472)), (837/274877906944), by norm_num⟩
  | 2 => ⟨((-66768725125/2199023255552), (42311751519/2199023255552)), (1103/274877906944), by norm_num⟩
  | 3 => ⟨((-123774787381/35184372088832), (-3381256927/8796093022208)), (60211/17592186044416), by norm_num⟩
  | 4 => ⟨((-19061682673/35184372088832), (46514099533/70368744177664)), (154593/70368744177664), by norm_num⟩
  | 5 => ⟨((-17628874451/70368744177664), (-2904147621/140737488355328)), (81025/70368744177664), by norm_num⟩
  | 6 => ⟨((3038616403/1125899906842624), (-13002845209/562949953421312)), (2323375/4503599627370496), by norm_num⟩
  | 7 => ⟨((-1617224049/2251799813685248), (83640836601/18014398509481984)), (3665415/18014398509481984), by norm_num⟩
  | 8 => ⟨((-41941121233/36028797018963968), (-10244964175/18014398509481984)), (2596001/36028797018963968), by norm_num⟩
  | 9 => ⟨((50346536649/288230376151711744), (-34531916075/288230376151711744)), (6704647/288230376151711744), by norm_num⟩
  | 10 => ⟨((-12238356961/2305843009213693952), (96216293901/2305843009213693952)), (1998947/288230376151711744), by norm_num⟩
  | 11 => ⟨((-61275095781/9223372036854775808), (-25682025167/4611686018427387904)), (8906683/4611686018427387904), by norm_num⟩
  | 12 => ⟨((59133852833/36893488147419103232), (-2213061869/4611686018427387904)), (2342225/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39256704879/274877906944), (7718133211/68719476736)), (309/274877906944), by norm_num⟩
  | 1 => ⟨((-4148504495/549755813888), (17748841731/137438953472)), (1675/549755813888), by norm_num⟩
  | 2 => ⟨((-66768725125/2199023255552), (42311751519/2199023255552)), (8825/2199023255552), by norm_num⟩
  | 3 => ⟨((-123774787381/35184372088832), (-3381256927/8796093022208)), (15053/4398046511104), by norm_num⟩
  | 4 => ⟨((-19061682673/35184372088832), (46514099533/70368744177664)), (38649/17592186044416), by norm_num⟩
  | 5 => ⟨((-17628874451/70368744177664), (-2904147621/140737488355328)), (20257/17592186044416), by norm_num⟩
  | 6 => ⟨((3038616403/1125899906842624), (-13002845209/562949953421312)), (580889/1125899906842624), by norm_num⟩
  | 7 => ⟨((-1617224049/2251799813685248), (83640836601/18014398509481984)), (458267/2251799813685248), by norm_num⟩
  | 8 => ⟨((-41941121233/36028797018963968), (-10244964175/18014398509481984)), (5194885/72057594037927936), by norm_num⟩
  | 9 => ⟨((50346536649/288230376151711744), (-34531916075/288230376151711744)), (6716177/288230376151711744), by norm_num⟩
  | 10 => ⟨((-12238356961/2305843009213693952), (96216293901/2305843009213693952)), (8041905/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-61275095781/9223372036854775808), (-25682025167/4611686018427387904)), (18182301/9223372036854775808), by norm_num⟩
  | 12 => ⟨((59133852833/36893488147419103232), (-2213061869/4611686018427387904)), (5053385/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile009Gamma
