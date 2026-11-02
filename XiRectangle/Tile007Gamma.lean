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
namespace Reinmann.XiRectangle.Tile007Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/128))
  have he : value ((3/4), (423/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((876544/11902705), (-108288/11902705)), 0, by norm_num⟩
  | 1 => ⟨((-378301546496/141674386317025), (94919196672/141674386317025)), 0, by norm_num⟩
  | 2 => ⟨((53633933481/562949953421312), (-1295348971/35184372088832)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-30089409491/9007199254740992), (32227695851/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((66216222249/576460752303423488), (-46733091185/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-71218499441/18446744073709551616), (64703319731/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((37248376927/295147905179352825856), (-5412838137/36893488147419103232)), (5/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-37585645247/9444732965739290427392), (7055585865/1180591620717411303424)), (1/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((9017509741/75557863725914323419136), (-71978698629/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-8005758999/2417851639229258349412352), (22515368999/2417851639229258349412352)), (15/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((24622333093/309485009821345068724781056), (-110778928907/309485009821345068724781056)), (21/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-6443261215/4951760157141521099596496896), (33528146305/2475880078570760549798248448)), (15/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-2169039533/158456325028528675187087900672), (-79948910867/158456325028528675187087900672)), (21/158456325028528675187087900672), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (423/256)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (423/256)))⁻¹=value ((876544/11902705), (-108288/11902705)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((876544/11902705), (-108288/11902705))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89368328371/34359738368), (1055848325/8589934592)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((438272/11902705), (-54144/11902705)), 0, by norm_num⟩
  | 2 => ⟨((-94575386624/141674386317025), (23729799168/141674386317025)), 0, by norm_num⟩
  | 3 => ⟨((17877977827/1125899906842624), (-27634111381/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-30089409491/72057594037927936), (32227695851/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((52972977799/4611686018427387904), (-9346618237/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-47478999627/147573952589676412928), (43135546487/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((42569573631/4722366482869645213696), (-773262591/73786976294838206464)), (3/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-37585645247/151115727451828646838272), (7055585865/18889465931478580854784)), (1/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((32062256857/4835703278458516698824704), (-7997633181/604462909807314587353088)), (5/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-25618428797/154742504910672534362390528), (72049180797/154742504910672534362390528)), (13/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((4476787835/1237940039285380274899124224), (-80566493751/4951760157141521099596496896)), (17/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-8591014953/158456325028528675187087900672), (89408390147/158456325028528675187087900672)), (21/158456325028528675187087900672), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (9/4096)), 0, by norm_num⟩
  | 45 => ⟨((21329149861/816127672320), (-17883/6029312)), 0, by norm_num⟩
  | 44 => ⟨((-10230380842787/383035920875520), (25174710181/7902739824640)), 0, by norm_num⟩
  | 43 => ⟨((120105052433/4398046511104), (-7214723435/2199023255552)), (1/4398046511104), by norm_num⟩
  | 42 => ⟨((-61464988945/2199023255552), (3692689543/1099511627776)), (1/2199023255552), by norm_num⟩
  | 41 => ⟨((31478057119/1099511627776), (-3779622201/1099511627776)), (1/2199023255552), by norm_num⟩
  | 40 => ⟨((-64523664491/2199023255552), (7741759903/2199023255552)), (1/2199023255552), by norm_num⟩
  | 39 => ⟨((33085811175/1099511627776), (-7933587093/2199023255552)), (1/1099511627776), by norm_num⟩
  | 38 => ⟨((-67906001517/2199023255552), (2033811449/549755813888)), (1/2199023255552), by norm_num⟩
  | 37 => ⟨((34866875213/1099511627776), (-4173721169/1099511627776)), (1/2199023255552), by norm_num⟩
  | 36 => ⟨((-71662619989/2199023255552), (66961017/17179869184)), (1/2199023255552), by norm_num⟩
  | 35 => ⟨((73701243521/2199023255552), (-8806886497/2199023255552)), (1/1099511627776), by norm_num⟩
  | 34 => ⟨((-75859264599/2199023255552), (9056116635/2199023255552)), (1/2199023255552), by norm_num⟩
  | 33 => ⟨((78147490341/2199023255552), (-4659933997/1099511627776)), (1/2199023255552), by norm_num⟩
  | 32 => ⟨((-1259032387/34359738368), (4799724085/1099511627776)), (1/2199023255552), by norm_num⟩
  | 31 => ⟨((20791181213/549755813888), (-1237040831/274877906944)), (1/2199023255552), by norm_num⟩
  | 30 => ⟨((-85922979513/2199023255552), (5106080337/1099511627776)), (1/2199023255552), by norm_num⟩
  | 29 => ⟨((88870501957/2199023255552), (-10548826247/2199023255552)), (1/2199023255552), by norm_num⟩
  | 28 => ⟨((-5751716789/137438953472), (2727113865/549755813888)), (1/1099511627776), by norm_num⟩
  | 27 => ⟨((95417029945/2199023255552), (-5646740881/1099511627776)), (1/2199023255552), by norm_num⟩
  | 26 => ⟨((-99065879371/2199023255552), (11706695169/2199023255552)), (1/2199023255552), by norm_num⟩
  | 25 => ⟨((103004958269/2199023255552), (-6075655045/1099511627776)), (1/2199023255552), by norm_num⟩
  | 24 => ⟨((-107270336117/2199023255552), (6315524625/1099511627776)), (1/2199023255552), by norm_num⟩
  | 23 => ⟨((111904319077/2199023255552), (-6575124179/1099511627776)), (1/2199023255552), by norm_num⟩
  | 22 => ⟨((-58478429603/1099511627776), (857124235/137438953472)), (1/2199023255552), by norm_num⟩
  | 21 => ⟨((61243681981/1099511627776), (-14328259575/2199023255552)), (1/2199023255552), by norm_num⟩
  | 20 => ⟨((-32141761323/549755813888), (3750045495/549755813888)), (1/1099511627776), by norm_num⟩
  | 19 => ⟨((67641002945/1099511627776), (-7869138483/1099511627776)), (1/549755813888), by norm_num⟩
  | 18 => ⟨((-71368673755/1099511627776), (8276417311/1099511627776)), (1/1099511627776), by norm_num⟩
  | 17 => ⟨((2360354991/34359738368), (-136378103/17179869184)), (1/1099511627776), by norm_num⟩
  | 16 => ⟨((-40104983207/549755813888), (2308051429/274877906944)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((21376699803/274877906944), (-2449515261/274877906944)), (1/549755813888), by norm_num⟩
  | 14 => ⟨((-91553143779/1099511627776), (10437908469/1099511627776)), (1/1099511627776), by norm_num⟩
  | 13 => ⟨((98520316871/1099511627776), (-11167298415/1099511627776)), (1/1099511627776), by norm_num⟩
  | 12 => ⟨((-13329524373/137438953472), (12006474261/1099511627776)), (1/1099511627776), by norm_num⟩
  | 11 => ⟨((58105338423/549755813888), (-1622786291/137438953472)), (1/549755813888), by norm_num⟩
  | 10 => ⟨((-63838138277/549755813888), (7065578053/549755813888)), (1/274877906944), by norm_num⟩
  | 9 => ⟨((17706937787/137438953472), (-7751855699/549755813888)), (1/274877906944), by norm_num⟩
  | 8 => ⟨((-39769554507/274877906944), (4293137911/274877906944)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((5668700779/34359738368), (-9622807731/549755813888)), (1/549755813888), by norm_num⟩
  | 6 => ⟨((-13189068361/68719476736), (2736346049/137438953472)), (1/549755813888), by norm_num⟩
  | 5 => ⟨((985402101/4294967296), (-793260277/34359738368)), (1/274877906944), by norm_num⟩
  | 4 => ⟨((-39205414733/137438953472), (7554046125/274877906944)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((51855064067/137438953472), (-4668469221/137438953472)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((-38372414219/68719476736), (3060535085/68719476736)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((74698884943/68719476736), (-4464895213/68719476736)), (1/68719476736), by norm_num⟩
  | 0 => ⟨((-47176757819/274877906944), (1055848325/8589934592)), (1/137438953472), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (423/4096)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (423/4096)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (423/4096))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((89368328371/34359738368), (1055848325/8589934592)), (1/34359738368), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (423/256))) (z:=((-21/128), (423/4096))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((89368328371/34359738368), (1055848325/8589934592))) (r:=(1/34359738368)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((71477420641/2147483648), (12627711723/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((61231449799/34359738368), (2189845847/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((1351443274752/141674386317025), (-172979914464/141674386317025)), 0, by norm_num⟩
  | 3 => ⟨((-67102798517/562949953421312), (8721190357/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((617455185/281474976710656), (-1978910835/2251799813685248)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-27382338705/576460752303423488), (30455465799/1152921504606846976)), (23/1152921504606846976), by norm_num⟩
  | 6 => ⟨((20625096743/18446744073709551616), (-30316258609/36893488147419103232)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-64904107267/2361183241434822606848), (61669968869/2361183241434822606848)), (85/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((3247874059/4722366482869645213696), (-63599977551/75557863725914323419136)), (107/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-41425026653/2417851639229258349412352), (66168321403/2417851639229258349412352)), (69/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((8013603171/19342813113834066795298816), (-69197147557/77371252455336267181195264)), (175/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-5777093105/618970019642690137449562112), (18135256913/618970019642690137449562112)), (229/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((1760731829/9903520314283042199192993792), (-76063093369/79228162514264337593543950336)), (145/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((42754826849/2147483648), (9079330539/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((44051580615/34359738368), (2189845847/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((1351443274752/141674386317025), (-172979914464/141674386317025)), 0, by norm_num⟩
  | 3 => ⟨((-67102798517/562949953421312), (8721190357/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((617455185/281474976710656), (-1978910835/2251799813685248)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-27382338705/576460752303423488), (30455465799/1152921504606846976)), (23/1152921504606846976), by norm_num⟩
  | 6 => ⟨((20625096743/18446744073709551616), (-30316258609/36893488147419103232)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-64904107267/2361183241434822606848), (61669968869/2361183241434822606848)), (85/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((3247874059/4722366482869645213696), (-63599977551/75557863725914323419136)), (107/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-41425026653/2417851639229258349412352), (66168321403/2417851639229258349412352)), (69/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((8013603171/19342813113834066795298816), (-69197147557/77371252455336267181195264)), (175/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-5777093105/618970019642690137449562112), (18135256913/618970019642690137449562112)), (229/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((1760731829/9903520314283042199192993792), (-76063093369/79228162514264337593543950336)), (145/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((89456464645/4294967296), (9079330539/2147483648)), (5/4294967296), by norm_num⟩
  | 1 => ⟨((44051580615/34359738368), (2189845847/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((1351443274752/141674386317025), (-172979914464/141674386317025)), 0, by norm_num⟩
  | 3 => ⟨((-67102798517/562949953421312), (8721190357/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((617455185/281474976710656), (-1978910835/2251799813685248)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-27382338705/576460752303423488), (30455465799/1152921504606846976)), (23/1152921504606846976), by norm_num⟩
  | 6 => ⟨((20625096743/18446744073709551616), (-30316258609/36893488147419103232)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-64904107267/2361183241434822606848), (61669968869/2361183241434822606848)), (85/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((3247874059/4722366482869645213696), (-63599977551/75557863725914323419136)), (107/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-41425026653/2417851639229258349412352), (66168321403/2417851639229258349412352)), (69/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((8013603171/19342813113834066795298816), (-69197147557/77371252455336267181195264)), (175/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-5777093105/618970019642690137449562112), (18135256913/618970019642690137449562112)), (229/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((1760731829/9903520314283042199192993792), (-76063093369/79228162514264337593543950336)), (145/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((756603092992/141674386317025), (-189838393344/141674386317025)), 0, by norm_num⟩
  | 1 => ⟨((-53633933481/140737488355328), (1295348971/8796093022208)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((11283528559/562949953421312), (-1510673243/140737488355328)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-8277027781/9007199254740992), (46733091185/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((22255781075/576460752303423488), (-40439574831/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((-55872565391/36893488147419103232), (16238514411/9223372036854775808)), (3/18446744073709551616), by norm_num⟩
  | 6 => ⟨((4110929949/73786976294838206464), (-49389101055/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-9017509741/4722366482869645213696), (71978698629/18889465931478580854784)), (5/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((4503239437/75557863725914323419136), (-6332447531/37778931862957161709568)), (1/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-15388958183/9671406556917033397649408), (69236830567/9671406556917033397649408)), (13/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((8859484171/309485009821345068724781056), (-92202402339/309485009821345068724781056)), (19/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((3253559299/9903520314283042199192993792), (119923366301/9903520314283042199192993792)), (7/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-5766082635/79228162514264337593543950336), (-38141336077/79228162514264337593543950336)), (11/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((53633933481/140737488355328), (-1295348971/8796093022208)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-11283528559/281474976710656), (1510673243/70368744177664)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((24831083343/9007199254740992), (-8762454597/4503599627370496)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((-22255781075/144115188075855872), (40439574831/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((34920353369/4611686018427387904), (-40596286027/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-49331159387/147573952589676412928), (37041825791/73786976294838206464)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((15780642047/1180591620717411303424), (-15745340325/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-4503239437/9444732965739290427392), (101319160495/75557863725914323419136)), (15/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((17312577957/1208925819614629174706176), (-19472858597/302231454903657293676544)), (13/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-5537177607/19342813113834066795298816), (28813250731/9671406556917033397649408)), (11/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-1118411009/309485009821345068724781056), (-20611828583/154742504910672534362390528)), (19/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((17298247905/19807040628566084398385987584), (14303001029/2475880078570760549798248448)), (29/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-337587753/4951760157141521099596496896), (-19294532809/79228162514264337593543950336)), (23/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((30089409491/1125899906842624), (-32227695851/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-8277027781/2251799813685248), (2920818199/1125899906842624)), (3/18014398509481984), by norm_num⟩
  | 2 => ⟨((22255781075/72057594037927936), (-40439574831/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-46560471159/2305843009213693952), (54128381369/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((41109299489/36893488147419103232), (-61736376317/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-15780642047/295147905179352825856), (15745340325/147573952589676412928)), (1/73786976294838206464), by norm_num⟩
  | 6 => ⟨((21015117373/9444732965739290427392), (-29551421811/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-5770859319/75557863725914323419136), (51927622925/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((8305766411/4835703278458516698824704), (-168827641/9444732965739290427392)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((466004587/19342813113834066795298816), (17176523819/19342813113834066795298816)), (15/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-7928363623/1237940039285380274899124224), (-26222168553/618970019642690137449562112)), (13/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((337587753/618970019642690137449562112), (19294532809/9903520314283042199192993792)), (11/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-22932382777/633825300114114700748351602688), (-428673559/4951760157141521099596496896)), (19/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((66216222249/36028797018963968), (-46733091185/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((-22255781075/72057594037927936), (40439574831/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 2 => ⟨((34920353369/1152921504606846976), (-40596286027/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 3 => ⟨((-41109299489/18446744073709551616), (61736376317/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 4 => ⟨((39451605117/295147905179352825856), (-9840837703/36893488147419103232)), (1/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-31522676059/4722366482869645213696), (88654265433/4722366482869645213696)), (3/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((20198007617/75557863725914323419136), (-90873340119/75557863725914323419136)), (7/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-8305766411/1208925819614629174706176), (168827641/2361183241434822606848)), (15/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-2097020641/19342813113834066795298816), (-38647178593/9671406556917033397649408)), (1/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((38712713/1208925819614629174706176), (32777710691/154742504910672534362390528)), (1/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-29707722263/9903520314283042199192993792), (-106119930449/9903520314283042199192993792)), (29/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((17199287083/79228162514264337593543950336), (1286020677/2475880078570760549798248448)), (27/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-4375984859/316912650057057350374175801344), (-61314272821/2535301200456458802993406410752)), (3/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((71218499441/576460752303423488), (-64703319731/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 1 => ⟨((-55872565391/2305843009213693952), (64954057643/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 2 => ⟨((49331159387/18446744073709551616), (-74083651581/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-15780642047/73786976294838206464), (62981361299/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 4 => ⟨((31522676059/2361183241434822606848), (-11081783179/295147905179352825856)), (5/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-24237609139/37778931862957161709568), (54524004071/18889465931478580854784)), (1/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((726754561/37778931862957161709568), (-121015653069/604462909807314587353088)), (5/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((3355233025/9671406556917033397649408), (123670971497/9671406556917033397649408)), (3/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-17838818151/154742504910672534362390528), (-117999758489/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((14853861131/1237940039285380274899124224), (106119930449/2475880078570760549798248448)), (29/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-18919215791/19807040628566084398385987584), (-22633963915/9903520314283042199192993792)), (29/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((21004727323/316912650057057350374175801344), (73577127385/633825300114114700748351602688)), (7/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-42648072659/10141204801825835211973625643008), (-57076996939/10141204801825835211973625643008)), (27/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37248376927/4611686018427387904), (-5412838137/576460752303423488)), (5/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-4110929949/2305843009213693952), (24694550527/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((15780642047/73786976294838206464), (-62981361299/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-21015117373/1180591620717411303424), (59102843621/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 4 => ⟨((315593869/295147905179352825856), (-45436670059/9444732965739290427392)), (13/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-11628072975/302231454903657293676544), (30253913267/75557863725914323419136)), (19/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-1957219265/2417851639229258349412352), (-9017675005/302231454903657293676544)), (7/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((5946272717/19342813113834066795298816), (78666505659/38685626227668133590597632)), (17/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-22280791697/618970019642690137449562112), (-79589947837/618970019642690137449562112)), (21/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((15766013159/4951760157141521099596496896), (4715409149/618970019642690137449562112)), (3/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-38508666759/158456325028528675187087900672), (-67445700103/158456325028528675187087900672)), (13/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((42648072659/2535301200456458802993406410752), (57076996939/2535301200456458802993406410752)), (13/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-43919763831/40564819207303340847894502572032), (-11445858243/10141204801825835211973625643008)), (13/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37585645247/73786976294838206464), (-7055585865/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-36070038965/295147905179352825856), (17994674657/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 2 => ⟨((36025915497/2361183241434822606848), (-50659580247/1180591620717411303424)), (15/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-5770859319/4722366482869645213696), (12981905731/2361183241434822606848)), (17/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((8305766411/151115727451828646838272), (-86439752191/151115727451828646838272)), (7/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((1677616513/1208925819614629174706176), (15458871437/302231454903657293676544)), (23/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((-5946272717/9671406556917033397649408), (-78666505659/19342813113834066795298816)), (9/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((25463761939/309485009821345068724781056), (90959940385/309485009821345068724781056)), (23/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-20270588347/2475880078570760549798248448), (-48501351247/2475880078570760549798248448)), (15/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((13753095271/19807040628566084398385987584), (48175500073/39614081257132168796771975168)), (9/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((-16754599973/316912650057057350374175801344), (-5605776485/79228162514264337593543950336)), (21/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((37645511855/10141204801825835211973625643008), (39242942547/10141204801825835211973625643008)), (23/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-39638175177/162259276829213363391578010288128), (-32267766823/162259276829213363391578010288128)), (3/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9017509741/295147905179352825856), (-71978698629/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-36025915497/4722366482869645213696), (101319160495/4722366482869645213696)), (1/295147905179352825856), by norm_num⟩
  | 2 => ⟨((8656288979/9444732965739290427392), (-77891434387/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-2076441603/37778931862957161709568), (86439752191/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-2097020641/1208925819614629174706176), (-1207724331/18889465931478580854784)), (1/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((17838818151/19342813113834066795298816), (117999758487/19342813113834066795298816)), (25/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-22280791697/154742504910672534362390528), (-79589947837/154742504910672534362390528)), (21/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((20270588347/1237940039285380274899124224), (48501351247/1237940039285380274899124224)), (15/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-3868058045/2475880078570760549798248448), (-54197437583/19807040628566084398385987584)), (21/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((41886499933/316912650057057350374175801344), (28028882425/158456325028528675187087900672)), (25/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-3235161175/316912650057057350374175801344), (-26979523001/2535301200456458802993406410752)), (31/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((29728631383/40564819207303340847894502572032), (48401650233/81129638414606681695789005144064)), (9/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-64252313329/1298074214633706907132624082305024), (-40313153503/1298074214633706907132624082305024)), (39/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8005758999/4722366482869645213696), (-22515368999/4722366482869645213696)), (15/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((-1923619773/4722366482869645213696), (69236830567/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((692147201/18889465931478580854784), (-57626501461/151115727451828646838272)), (11/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((1864018347/1208925819614629174706176), (68706095275/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-38712713/37778931862957161709568), (-65555421381/9671406556917033397649408)), (1/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((14853861131/77371252455336267181195264), (6632495653/9671406556917033397649408)), (7/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-15766013159/618970019642690137449562112), (-75446546383/1237940039285380274899124224)), (3/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((13753095271/4951760157141521099596496896), (48175500073/9903520314283042199192993792)), (9/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-41886499933/158456325028528675187087900672), (-56057764851/158456325028528675187087900672)), (13/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((57513976445/2535301200456458802993406410752), (29977247779/1267650600228229401496703205376)), (17/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-72669987825/40564819207303340847894502572032), (-59157572507/40564819207303340847894502572032)), (43/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((42834875553/324518553658426726783156020576256), (6718858917/81129638414606681695789005144064)), (13/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-23792791835/2596148429267413814265248164610048), (-22252587483/5192296858534827628530496329220096)), (15/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((24622333093/302231454903657293676544), (-110778928907/302231454903657293676544)), (21/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((-2214871043/151115727451828646838272), (92202402339/604462909807314587353088)), (5/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-4368793/4722366482869645213696), (-82447314331/2417851639229258349412352)), (19/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((3964181811/4835703278458516698824704), (104888674211/19342813113834066795298816)), (7/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((-14853861131/77371252455336267181195264), (-106119930447/154742504910672534362390528)), (31/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((37838431581/1237940039285380274899124224), (90535855659/1237940039285380274899124224)), (29/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-19254333379/4951760157141521099596496896), (-33722850051/4951760157141521099596496896)), (13/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((16754599973/39614081257132168796771975168), (5605776485/9903520314283042199192993792)), (21/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((-3235161175/79228162514264337593543950336), (-26979523001/633825300114114700748351602688)), (31/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((72669987825/20282409603651670423947251286016), (14789393127/5070602400912917605986812821504)), (43/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((-11779590777/40564819207303340847894502572032), (-29562979235/162259276829213363391578010288128)), (29/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((14275675101/649037107316853453566312041152512), (6675776245/649037107316853453566312041152512)), (37/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((-16309771821/10384593717069655257060992658440192), (-21222290959/41538374868278621028243970633760768)), (11/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((219136/35708115), (-9024/11902705)), 0, by norm_num⟩
  | 1 => ⟨((-94575386624/425023158951075), (7909933056/141674386317025)), 0, by norm_num⟩
  | 2 => ⟨((17877977827/2251799813685248), (-27634111381/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-80238425309/288230376151711744), (42970261135/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((22072074083/2305843009213693952), (-31155394123/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-47478999627/147573952589676412928), (43135546487/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 6 => ⟨((49664502569/4722366482869645213696), (-1804279379/147573952589676412928)), (7/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-50114193663/151115727451828646838272), (2351861955/4722366482869645213696)), (11/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((24046692643/2417851639229258349412352), (-23992899543/1208925819614629174706176)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-2668586333/9671406556917033397649408), (60040983997/77371252455336267181195264)), (11/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((16414888729/2475880078570760549798248448), (-73852619271/2475880078570760549798248448)), (15/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-8591014953/79228162514264337593543950336), (89408390147/79228162514264337593543950336)), (21/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-2892052711/2535301200456458802993406410752), (-106598547823/2535301200456458802993406410752)), (29/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44741411147/2147483648), (18155404861/4294967296)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((11010983737/8589934592), (4383528425/68719476736)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((83976468997/8796093022208), (-5383367965/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-67259514191/562949953421312), (17526307005/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((39689569919/18014398509481984), (-31905974877/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-55135607095/1152921504606846976), (1924528891/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((10409549353/9223372036854775808), (-15383664227/18446744073709551616)), (37/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-65687141543/2361183241434822606848), (31422949923/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((52717444089/75557863725914323419136), (-16274883443/18889465931478580854784)), (27/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-10523043309/604462909807314587353088), (68044602153/2417851639229258349412352)), (139/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((32567377957/77371252455336267181195264), (-71505041909/77371252455336267181195264)), (11/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-23376841637/2475880078570760549798248448), (18833759961/618970019642690137449562112)), (231/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((13995477985/79228162514264337593543950336), (-19848574497/19807040628566084398385987584)), (73/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-38139686031/36028797018963968), (29476385473/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 1 => ⟨((64190740247/576460752303423488), (-34376208907/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 2 => ⟨((-70630637065/9223372036854775808), (12462157649/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((15826333209/36893488147419103232), (-28757030991/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-49664502569/2361183241434822606848), (57736940127/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((8769983891/9444732965739290427392), (-3292606737/2361183241434822606848)), (7/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-2805447475/75557863725914323419136), (89573491627/1208925819614629174706176)), (13/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((25618428797/19342813113834066795298816), (-18012295199/4835703278458516698824704)), (3/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-12311166547/309485009821345068724781056), (110778928907/618970019642690137449562112)), (5/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((7875097041/9903520314283042199192993792), (-10244711371/1237940039285380274899124224)), (1/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((3181257981/316912650057057350374175801344), (58629201303/158456325028528675187087900672)), (7/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-384405509/158456325028528675187087900672), (-5085511477/316912650057057350374175801344)), (21/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((15363993737/81129638414606681695789005144064), (54882226657/81129638414606681695789005144064)), (9/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89482817747/4294967296), (9077703309/2147483648)), (7/4294967296), by norm_num⟩
  | 1 => ⟨((22021969387/17179869184), (4383524327/68719476736)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((41988200819/4398046511104), (-10766688391/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-16814818175/140737488355328), (8763043803/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((39689191009/18014398509481984), (-31905093881/36028797018963968)), (19/36028797018963968), by norm_num⟩
  | 5 => ⟨((-13783634135/288230376151711744), (15395427269/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((41636827565/36893488147419103232), (-3845574361/4611686018427387904)), (19/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-65684014293/2361183241434822606848), (15709276195/590295810358705651712)), (87/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((52714438433/75557863725914323419136), (-32543005477/37778931862957161709568)), (109/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-42090250605/2417851639229258349412352), (68024592951/2417851639229258349412352)), (35/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((32568154631/77371252455336267181195264), (-71476414369/77371252455336267181195264)), (177/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-23382847973/2475880078570760549798248448), (37647654643/1237940039285380274899124224)), (29/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((14010481885/79228162514264337593543950336), (-4958793879/4951760157141521099596496896)), (293/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((53813818717/36893488147419103232), (-37979909027/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-18087237953/73786976294838206464), (32865178275/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 2 => ⟨((14189857877/590295810358705651712), (-65985074431/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-16704731221/9444732965739290427392), (50173055039/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((32062256857/302231454903657293676544), (-63981065447/302231454903657293676544)), (7/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((-25618428797/4835703278458516698824704), (18012295199/1208925819614629174706176)), (11/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((8207444365/38685626227668133590597632), (-73852619271/77371252455336267181195264)), (3/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((-3375041589/618970019642690137449562112), (8781181175/154742504910672534362390528)), (7/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-3408490693/39614081257132168796771975168), (-125634002791/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((1006776333/39614081257132168796771975168), (53276786901/316912650057057350374175801344)), (27/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-3017927341/1267650600228229401496703205376), (-10780437379/1267650600228229401496703205376)), (25/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((436807291/2535301200456458802993406410752), (66889405625/162259276829213363391578010288128)), (23/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-28450847591/2596148429267413814265248164610048), (-49830012197/2596148429267413814265248164610048)), (21/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89482817753/4294967296), (9077703307/2147483648)), (1/536870912), by norm_num⟩
  | 1 => ⟨((88087877531/68719476736), (2191762171/34359738368)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((83976401849/8796093022208), (-10766688637/8796093022208)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-2101852303/17592186044416), (17526089101/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((4961149115/2251799813685248), (-7976275377/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-6891817831/144115188075855872), (7697717929/288230376151711744)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((650575553/576460752303423488), (-3845578763/4611686018427387904)), (39/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-2052625849/73786976294838206464), (31418619385/1180591620717411303424)), (11/295147905179352825856), by norm_num⟩
  | 8 => ⟨((13178607983/18889465931478580854784), (-32543125291/37778931862957161709568)), (55/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-10522547289/604462909807314587353088), (68024999421/2417851639229258349412352)), (141/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((32567970431/77371252455336267181195264), (-71477072355/77371252455336267181195264)), (89/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-23382421403/2475880078570760549798248448), (75296329937/2475880078570760549798248448)), (233/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((7004806817/39614081257132168796771975168), (-79342222755/79228162514264337593543950336)), (147/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-22703772603/4722366482869645213696), (26394029773/4722366482869645213696)), (7/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((40091354931/37778931862957161709568), (-60207666047/37778931862957161709568)), (1/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((-38474708229/302231454903657293676544), (9597159817/37778931862957161709568)), (5/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((12809214399/1208925819614629174706176), (-72049180795/2417851639229258349412352)), (11/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((-12311166547/19342813113834066795298816), (55389464453/19342813113834066795298816)), (17/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((7087587337/309485009821345068724781056), (-36880960935/154742504910672534362390528)), (3/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((2385943485/4951760157141521099596496896), (43971900977/2475880078570760549798248448)), (9/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((-3624394799/19807040628566084398385987584), (-47949108211/39614081257132168796771975168)), (11/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((27161346069/1267650600228229401496703205376), (97023936411/1267650600228229401496703205376)), (27/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((-38439041607/20282409603651670423947251286016), (-91972932735/20282409603651670423947251286016)), (15/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((46943898525/324518553658426726783156020576256), (41109760063/162259276829213363391578010288128)), (33/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-6498753929/649037107316853453566312041152512), (-69579577221/5192296858534827628530496329220096)), (1/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((53540283527/83076749736557242056487941267521536), (13953046239/20769187434139310514121985316880384)), (33/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89482817753/4294967296), (9077703307/2147483648)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((88087877531/68719476736), (2191762171/34359738368)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((10497050231/1099511627776), (-10766688635/8796093022208)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-33629636845/281474976710656), (4381522271/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((79378385817/36028797018963968), (-31905101405/36028797018963968)), (21/36028797018963968), by norm_num⟩
  | 5 => ⟨((-27567271311/576460752303423488), (30790871441/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 6 => ⟨((20818417705/18446744073709551616), (-30764629449/36893488147419103232)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-4105251725/147573952589676412928), (7854654489/295147905179352825856)), (89/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((52714433551/75557863725914323419136), (-65086244799/75557863725914323419136)), (111/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-21045096869/1208925819614629174706176), (68024988457/2417851639229258349412352)), (71/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((32567981623/77371252455336267181195264), (-4467315797/4835703278458516698824704)), (179/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-11691223097/1237940039285380274899124224), (75296296759/2475880078570760549798248448)), (117/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((7004832347/39614081257132168796771975168), (-9917771191/9903520314283042199192993792)), (295/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7772668329/302231454903657293676544), (-62042245283/1208925819614629174706176)), (5/604462909807314587353088), by norm_num⟩
  | 1 => ⟨((-31052640967/4835703278458516698824704), (87332340359/4835703278458516698824704)), (15/4835703278458516698824704), by norm_num⟩
  | 2 => ⟨((14922626119/19342813113834066795298816), (-67138744791/19342813113834066795298816)), (13/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((-3579589565/77371252455336267181195264), (18626747947/38685626227668133590597632)), (1/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((-1807532943/1237940039285380274899124224), (-133248184775/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 5 => ⟨((15376220359/19807040628566084398385987584), (50855114769/9903520314283042199192993792)), (23/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((-9602496085/79228162514264337593543950336), (-68602783321/158456325028528675187087900672)), (19/158456325028528675187087900672), by norm_num⟩
  | 7 => ⟨((17472291639/1267650600228229401496703205376), (10451469629/316912650057057350374175801344)), (27/2535301200456458802993406410752), by norm_num⟩
  | 8 => ⟨((-26672669617/20282409603651670423947251286016), (-46715636435/20282409603651670423947251286016)), (19/20282409603651670423947251286016), by norm_num⟩
  | 9 => ⟨((18052094247/162259276829213363391578010288128), (48319150847/324518553658426726783156020576256)), (23/324518553658426726783156020576256), by norm_num⟩
  | 10 => ⟨((-44616902939/5192296858534827628530496329220096), (-23255077065/2596148429267413814265248164610048)), (7/1298074214633706907132624082305024), by norm_num⟩
  | 11 => ⟨((51249357805/83076749736557242056487941267521536), (20859970471/41538374868278621028243970633760768)), (1/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((-55382465361/1329227995784915872903807060280344576), (-8687009509/332306998946228968225951765070086144)), (17/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89482817753/4294967296), (9077703307/2147483648)), (5/2147483648), by norm_num⟩
  | 1 => ⟨((88087877531/68719476736), (2191762171/34359738368)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((10497050231/1099511627776), (-10766688635/8796093022208)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((-33629636845/281474976710656), (4381522271/140737488355328)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((79378385817/36028797018963968), (-31905101407/36028797018963968)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-55134542621/1152921504606846976), (30790871447/1152921504606846976)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((20818417703/18446744073709551616), (-30764629465/36893488147419103232)), (41/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-65684027567/2361183241434822606848), (31418617995/1180591620717411303424)), (45/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((13178608363/18889465931478580854784), (-65086244973/75557863725914323419136)), (7/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-42090193469/2417851639229258349412352), (68024988817/2417851639229258349412352)), (143/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((16283990479/38685626227668133590597632), (-71477053445/77371252455336267181195264)), (45/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-23382444667/2475880078570760549798248448), (37648149001/1237940039285380274899124224)), (235/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((14009661393/79228162514264337593543950336), (-79342171599/79228162514264337593543950336)), (37/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-24173561077/154742504910672534362390528), (54379923987/77371252455336267181195264)), (21/154742504910672534362390528), by norm_num⟩
  | 1 => ⟨((135906395/4835703278458516698824704), (-90521901233/309485009821345068724781056)), (5/77371252455336267181195264), by norm_num⟩
  | 2 => ⟨((1098026605/618970019642690137449562112), (20236152897/309485009821345068724781056)), (5/309485009821345068724781056), by norm_num⟩
  | 3 => ⟨((-15567719073/9903520314283042199192993792), (-102976950345/9903520314283042199192993792)), (7/2475880078570760549798248448), by norm_num⟩
  | 4 => ⟨((29166262833/79228162514264337593543950336), (104185765437/79228162514264337593543950336)), (31/79228162514264337593543950336), by norm_num⟩
  | 5 => ⟨((-18574390035/316912650057057350374175801344), (-22221432349/158456325028528675187087900672)), (15/316912650057057350374175801344), by norm_num⟩
  | 6 => ⟨((18903399697/2535301200456458802993406410752), (33108210027/2535301200456458802993406410752)), (27/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((-32898453955/40564819207303340847894502572032), (-11007208759/10141204801825835211973625643008)), (11/20282409603651670423947251286016), by norm_num⟩
  | 8 => ⟨((50819142743/649037107316853453566312041152512), (26487788327/324518553658426726783156020576256)), (31/649037107316853453566312041152512), by norm_num⟩
  | 9 => ⟨((-557386631/81129638414606681695789005144064), (-29039676841/5192296858534827628530496329220096)), (43/10384593717069655257060992658440192), by norm_num⟩
  | 10 => ⟨((11564893385/20769187434139310514121985316880384), (7256039481/20769187434139310514121985316880384)), (29/83076749736557242056487941267521536), by norm_num⟩
  | 11 => ⟨((-56061934125/1329227995784915872903807060280344576), (-26216408361/1329227995784915872903807060280344576)), (37/1329227995784915872903807060280344576), by norm_num⟩
  | 12 => ⟨((32025012721/10633823966279326983230456482242756608), (20835488853/21267647932558653966460912964485513216)), (11/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89482817753/4294967296), (9077703307/2147483648)), (11/4294967296), by norm_num⟩
  | 1 => ⟨((88087877531/68719476736), (2191762171/34359738368)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((10497050231/1099511627776), (-10766688635/8796093022208)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-33629636845/281474976710656), (4381522271/140737488355328)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((79378385817/36028797018963968), (-31905101407/36028797018963968)), (23/36028797018963968), by norm_num⟩
  | 5 => ⟨((-55134542621/1152921504606846976), (30790871447/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 6 => ⟨((20818417703/18446744073709551616), (-30764629465/36893488147419103232)), (21/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-65684027569/2361183241434822606848), (62837235987/2361183241434822606848)), (91/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((26357216729/37778931862957161709568), (-65086244967/75557863725914323419136)), (113/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-21045096743/1208925819614629174706176), (68024988803/2417851639229258349412352)), (9/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((32567981001/77371252455336267181195264), (-35738526709/38685626227668133590597632)), (181/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-23382444771/2475880078570760549798248448), (75296297953/2475880078570760549798248448)), (59/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((218900963/1237940039285380274899124224), (-79342171521/79228162514264337593543950336)), (297/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-68318607997835/131072), (-16195162626181/16384)), (2171093/262144), by norm_num⟩
  | 1 => ⟨((-9681333171/16), (-41610293157/32)), (725/64), by norm_num⟩
  | 2 => ⟨((-705050861/2), (-6892037027/8)), (251/32), by norm_num⟩
  | 3 => ⟨((-2194064743/16), (-49060096371/128)), (935/256), by norm_num⟩
  | 4 => ⟨((-5114859639/128), (-32975371583/256)), (661/512), by norm_num⟩
  | 5 => ⟨((-18991226897/2048), (-71425957217/2048)), (755/2048), by norm_num⟩
  | 6 => ⟨((-14556071199/8192), (-32454239631/4096)), (363/4096), by norm_num⟩
  | 7 => ⟨((-9412410343/32768), (-12725047573/8192)), (1209/65536), by norm_num⟩
  | 8 => ⟨((-10374051315/262144), (-35155321809/131072)), (445/131072), by norm_num⟩
  | 9 => ⟨((-4859592135/1048576), (-43442140455/1048576)), (589/1048576), by norm_num⟩
  | 10 => ⟨((-7549420563/16777216), (-97230070531/16777216)), (709/8388608), by norm_num⟩
  | 11 => ⟨((-4448282371/134217728), (-99515573555/134217728)), (49/4194304), by norm_num⟩
  | 12 => ⟨((-37757617/33554432), (-93917273607/1073741824)), (1607/1073741824), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((805557411898151/5070602400912917605986812821504), (-2678235074235/10141204801825835211973625643008)), (3337/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((226843395318071/79228162514264337593543950336), (-3289387091349/633825300114114700748351602688)), (257/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((241282792836493/4951760157141521099596496896), (-927671792669/9903520314283042199192993792)), (145/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((966305886463841/1237940039285380274899124224), (-3951197454555/2475880078570760549798248448)), (2471/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((907162482239407/77371252455336267181195264), (-3960808216529/154742504910672534362390528)), (4955/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1590041789008095/9671406556917033397649408), (-930875053637/2417851639229258349412352)), (4659/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((647133050338521/302231454903657293676544), (-1634171178479/302231454903657293676544)), (4091/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((972768519519105/37778931862957161709568), (-2665205045381/37778931862957161709568)), (6675/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((670465436390219/2361183241434822606848), (-2007410936919/2361183241434822606848)), (5029/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((210155768073419/73786976294838206464), (-1387044675155/147573952589676412928)), (3477/295147905179352825856), by norm_num⟩
  | 8 => ⟨((949212623708645/36893488147419103232), (-1744296529219/18446744073709551616)), (4375/36893488147419103232), by norm_num⟩
  | 7 => ⟨((953628488556381/4611686018427387904), (-3953733281791/4611686018427387904)), (9923/9223372036854775808), by norm_num⟩
  | 6 => ⟨((26232161812157/18014398509481984), (-3990393693429/576460752303423488)), (1253/144115188075855872), by norm_num⟩
  | 5 => ⟨((317311020249511/36028797018963968), (-3533292656061/72057594037927936)), (8887/144115188075855872), by norm_num⟩
  | 4 => ⟨((1604439469844503/36028797018963968), (-2692243484713/9007199254740992)), (3391/9007199254740992), by norm_num⟩
  | 3 => ⟨((407922331414937/2251799813685248), (-13762393511797/9007199254740992)), (17373/9007199254740992), by norm_num⟩
  | 2 => ⟨((1258583021539359/2251799813685248), (-7112433086955/1125899906842624)), (563/70368744177664), by norm_num⟩
  | 1 => ⟨((332632207439147/281474976710656), (-1408240100509/70368744177664)), (14345/562949953421312), by norm_num⟩
  | 0 => ⟨((389577969489421/281474976710656), (-25039611671853/562949953421312)), (64409/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((389577969489421/281474976710656), (-25039611671853/562949953421312)), (245700840476607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((538642015518075/281474976710656), (-34656299419297/281474976710656)), (23003/140737488355328), by norm_num⟩
  | 2 => ⟨((513250174435481/140737488355328), (-16579927626033/35184372088832)), (11713/17592186044416), by norm_num⟩
  | 3 => ⟨((460125160296165/35184372088832), (-241858820862407/70368744177664)), (192941/35184372088832), by norm_num⟩
  | 4 => ⟨((87526093408711/549755813888), (-790729819175031/8796093022208)), (1593169/8796093022208), by norm_num⟩
  | 5 => ⟨((593265664185767/34359738368), (-983526035926259/34359738368)), (3100515/34359738368), by norm_num⟩
  | 6 => ⟨((-68318607997835/131072), (-16195162626181/16384)), (2171093/262144), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((89482817753/4294967296), (9077703307/2147483648)), (11/4294967296), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((90112/302833), (-108288/302833)), 0, by norm_num⟩
  | 1 => ⟨((1803059200/91707825889), (9758048256/91707825889)), 0, by norm_num⟩
  | 2 => ⟨((-609578400088064/27772156037443537), (-342033784897536/27772156037443537)), 0, by norm_num⟩
  | 3 => ⟨((48093462645/8796093022208), (-287521279/137438953472)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-7730833275/17592186044416), (45345972219/35184372088832)), (3/70368744177664), by norm_num⟩
  | 5 => ⟨((-2903533419/17592186044416), (-38044263313/140737488355328)), (5/281474976710656), by norm_num⟩
  | 6 => ⟨((41031742335/562949953421312), (12058158003/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 7 => ⟨((-57461759745/4503599627370496), (25756459481/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 8 => ⟨((-1321642207/9007199254740992), (-2242232351/562949953421312)), (7/9007199254740992), by norm_num⟩
  | 9 => ⟨((52887307945/72057594037927936), (40810805619/72057594037927936)), (19/72057594037927936), by norm_num⟩
  | 10 => ⟨((-7582645891/36028797018963968), (13535628461/288230376151711744)), (13/144115188075855872), by norm_num⟩
  | 11 => ⟨((3302606517/144115188075855872), (-51438244959/1152921504606846976)), (35/1152921504606846976), by norm_num⟩
  | 12 => ⟨((21063152579/4611686018427387904), (49507579199/4611686018427387904)), (47/4611686018427387904), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (423/256)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (423/256)))⁻¹=value ((90112/302833), (-108288/302833)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((90112/302833), (-108288/302833))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((155648/548593), (-108288/548593)), 0, by norm_num⟩
  | 1 => ⟨((-6250004480/300954279649), (16854810624/300954279649)), 0, by norm_num⟩
  | 2 => ⟨((-426186517774336/165101411135483857), (-1650109024567296/165101411135483857)), 0, by norm_num⟩
  | 3 => ⟨((23795454153/17592186044416), (10230408431/8796093022208)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-43160417901/140737488355328), (-2216299091/70368744177664)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((52482112731/1125899906842624), (-29047620307/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 6 => ⟨((-4578282237/1125899906842624), (9300507871/1125899906842624)), (9/9007199254740992), by norm_num⟩
  | 7 => ⟨((-8590205787/36028797018963968), (-113359286815/72057594037927936)), (9/36028797018963968), by norm_num⟩
  | 8 => ⟨((6812676771/36028797018963968), (57542527395/288230376151711744)), (9/144115188075855872), by norm_num⟩
  | 9 => ⟨((-107286832453/2305843009213693952), (-2783967501/288230376151711744)), (35/2305843009213693952), by norm_num⟩
  | 10 => ⟨((17417961111/2305843009213693952), (-14858601411/4611686018427387904)), (35/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-13901502179/18446744073709551616), (44368221527/36893488147419103232)), (35/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-1739227261/147573952589676412928), (-36152691267/147573952589676412928)), (17/73786976294838206464), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (423/256)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (423/256)))⁻¹=value ((155648/548593), (-108288/548593)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((155648/548593), (-108288/548593))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2299461632/166132063969), (-26612858880/166132063969)), 0, by norm_num⟩
  | 1 => ⟨((44451273481/1099511627776), (3463400045/68719476736)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-85180936015/4398046511104), (-2552176217/1099511627776)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((72391471137/17592186044416), (-28631770287/8796093022208)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-4671562075/35184372088832), (92908243529/70368744177664)), (3/70368744177664), by norm_num⟩
  | 5 => ⟨((-29788531443/140737488355328), (-34413310775/140737488355328)), (3/140737488355328), by norm_num⟩
  | 6 => ⟨((86641766907/1125899906842624), (2757650133/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 7 => ⟨((-28193992011/2251799813685248), (14649468597/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 8 => ⟨((-6049622799/18014398509481984), (-37673921597/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 9 => ⟨((56240021459/72057594037927936), (20753398747/36028797018963968)), (11/36028797018963968), by norm_num⟩
  | 10 => ⟨((-62838412267/288230376151711744), (14464291049/288230376151711744)), (29/288230376151711744), by norm_num⟩
  | 11 => ⟨((13644848011/576460752303423488), (-26412375941/576460752303423488)), (19/576460752303423488), by norm_num⟩
  | 12 => ⟨((21117503431/4611686018427387904), (50637350801/4611686018427387904)), (25/2305843009213693952), by norm_num⟩
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
  | 0 => ⟨((27/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((8192/34275), (-12032/102825)), 0, by norm_num⟩
  | 1 => ⟨((-229605376/10572980625), (98566144/3524326875)), 0, by norm_num⟩
  | 2 => ⟨((115829899264/120796303640625), (-5014848274432/1087166732765625)), 0, by norm_num⟩
  | 3 => ⟨((21855025123/140737488355328), (85476355675/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-30450972213/562949953421312), (-71488733471/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((91685042639/9007199254740992), (19919959513/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-106301211325/72057594037927936), (4825619569/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((49684351371/288230376151711744), (-13592128385/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 8 => ⟨((-17388021237/1152921504606846976), (12311037297/576460752303423488)), (5/1152921504606846976), by norm_num⟩
  | 9 => ⟨((10197925283/18446744073709551616), (-7919521291/2305843009213693952)), (15/18446744073709551616), by norm_num⟩
  | 10 => ⟨((9952389587/73786976294838206464), (32671873163/73786976294838206464)), (23/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-6201778793/147573952589676412928), (-26577069909/590295810358705651712)), (17/590295810358705651712), by norm_num⟩
  | 12 => ⟨((72311983865/9444732965739290427392), (27594756943/9444732965739290427392)), (49/9444732965739290427392), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (423/256)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (423/256)))⁻¹=value ((8192/34275), (-12032/102825)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((8192/34275), (-12032/102825))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-87898116325376/5694176492537475), (-681704742191104/17082529477612425)), 0, by norm_num⟩
  | 1 => ⟨((86815783313/4398046511104), (49174372689/4398046511104)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-1087668123/137438953472), (13460480469/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((51327895125/35184372088832), (-4189988311/2199023255552)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((4215356637/70368744177664), (45328248389/70368744177664)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((-34916216743/281474976710656), (-15079929751/140737488355328)), (7/562949953421312), by norm_num⟩
  | 6 => ⟨((89559092717/2251799813685248), (-808432179/281474976710656)), (11/2251799813685248), by norm_num⟩
  | 7 => ⟨((-13634472577/2251799813685248), (65258075801/9007199254740992)), (15/9007199254740992), by norm_num⟩
  | 8 => ⟨((-1215956127/4503599627370496), (-9819941405/4503599627370496)), (5/9007199254740992), by norm_num⟩
  | 9 => ⟨((59632570619/144115188075855872), (41955304329/144115188075855872)), (27/144115188075855872), by norm_num⟩
  | 10 => ⟨((-16244195221/144115188075855872), (7760289071/288230376151711744)), (9/144115188075855872), by norm_num⟩
  | 11 => ⟨((28110088511/2305843009213693952), (-6782895893/288230376151711744)), (47/2305843009213693952), by norm_num⟩
  | 12 => ⟨((21207162869/9223372036854775808), (25890298203/4611686018427387904)), (31/4611686018427387904), by norm_num⟩
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
  | 0 => ⟨((35/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((286720/1433329), (-108288/1433329)), 0, by norm_num⟩
  | 1 => ⟨((-35241033728/2054432022241), (31048335360/2054432022241)), 0, by norm_num⟩
  | 2 => ⟨((3371073525514240/2944676996006670289), (-6359179887378432/2944676996006670289)), 0, by norm_num⟩
  | 3 => ⟨((-1158440581/35184372088832), (72969807435/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-7318026553/1125899906842624), (-15296882221/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((7550481623/4503599627370496), (44536263099/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((-75249934787/288230376151711744), (-414198831/2251799813685248)), (1/36028797018963968), by norm_num⟩
  | 7 => ⟨((76233202475/2305843009213693952), (19681450473/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-4184114171/1152921504606846976), (7289535201/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 9 => ⟨((12840972487/36893488147419103232), (-26063758477/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-16611206845/590295810358705651712), (18188557889/590295810358705651712)), (15/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((31179584533/18889465931478580854784), (-39147007755/9444732965739290427392)), (17/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-1287933547/151115727451828646838272), (72069524797/151115727451828646838272)), (19/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (423/256)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (423/256)))⁻¹=value ((286720/1433329), (-108288/1433329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((286720/1433329), (-108288/1433329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-53680987375/8796093022208), (-29979684987/4398046511104)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((12449301277/2199023255552), (21049750737/17592186044416)), (3/17592186044416), by norm_num⟩
  | 2 => ⟨((-73144336681/35184372088832), (35120401989/35184372088832)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((1398975731/4398046511104), (-47128102589/70368744177664)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((3809259305/70368744177664), (57232542975/281474976710656)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((-51796367737/1125899906842624), (-34175798733/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 6 => ⟨((15184901193/1125899906842624), (-10273376851/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 7 => ⟨((-17353457193/9007199254740992), (47636721913/18014398509481984)), (13/18014398509481984), by norm_num⟩
  | 8 => ⟨((-18149315041/144115188075855872), (-108524824077/144115188075855872)), (17/72057594037927936), by norm_num⟩
  | 9 => ⟨((2626661475/18014398509481984), (1757043857/18014398509481984)), (23/288230376151711744), by norm_num⟩
  | 10 => ⟨((-89424216051/2305843009213693952), (5565202869/576460752303423488)), (61/2305843009213693952), by norm_num⟩
  | 11 => ⟨((9626708851/2305843009213693952), (-37165808039/4611686018427387904)), (79/9223372036854775808), by norm_num⟩
  | 12 => ⟨((7110723399/9223372036854775808), (17645038875/9223372036854775808)), (105/36893488147419103232), by norm_num⟩
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
  | 0 => ⟨((43/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((352256/2072305), (-108288/2072305)), 0, by norm_num⟩
  | 1 => ⟨((-56178999296/4294448013025), (38145097728/4294448013025)), 0, by norm_num⟩
  | 2 => ⟨((7829366616621056/8899406089631772625), (-9760175510519808/8899406089631772625)), 0, by norm_num⟩
  | 3 => ⟨((-12980979021/281474976710656), (65413565061/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((7959258347/9007199254740992), (-49903251281/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((15449752891/72057594037927936), (34762577453/36028797018963968)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-25036870787/576460752303423488), (-11010748961/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 7 => ⟨((26229181303/4611686018427387904), (49425994263/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-91998098909/147573952589676412928), (-45282878207/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | 9 => ⟨((72017342321/1180591620717411303424), (5779916963/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-51383039143/9444732965739290427392), (3596568175/4722366482869645213696)), (13/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((66866811545/151115727451828646838272), (-31261776547/151115727451828646838272)), (3/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-38930486215/1208925819614629174706176), (17616153653/604462909807314587353088)), (11/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (423/256)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (423/256)))⁻¹=value ((352256/2072305), (-108288/2072305)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((352256/2072305), (-108288/2072305))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-49032029831/35184372088832), (-3693481671/4398046511104)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((20498932413/17592186044416), (-4044330251/70368744177664)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-28059380447/70368744177664), (11035042885/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((6300649165/140737488355328), (-47158001569/281474976710656)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((22967307923/1125899906842624), (53078379039/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-6964580979/562949953421312), (-28055236873/4503599627370496)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((61025170099/18014398509481984), (-1995757955/2251799813685248)), (13/18014398509481984), by norm_num⟩
  | 7 => ⟨((-32719137581/72057594037927936), (51449726031/72057594037927936)), (17/72057594037927936), by norm_num⟩
  | 8 => ⟨((-23531317395/576460752303423488), (-55908500019/288230376151711744)), (11/144115188075855872), by norm_num⟩
  | 9 => ⟨((22147083789/576460752303423488), (28107649475/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-23035337625/2305843009213693952), (23974294441/9223372036854775808)), (77/9223372036854775808), by norm_num⟩
  | 11 => ⟨((39464556333/36893488147419103232), (-76369128595/36893488147419103232)), (25/9223372036854775808), by norm_num⟩
  | 12 => ⟨((14328277475/73786976294838206464), (72131795297/147573952589676412928)), (133/147573952589676412928), by norm_num⟩
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
  | 0 => ⟨((51/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((139264/947451), (-12032/315817)), 0, by norm_num⟩
  | 1 => ⟨((-9045770240/897663397401), (1675624448/299221132467)), 0, by norm_num⟩
  | 2 => ⟨((539150063239168/850492083530974851), (-57032145108992/94499120392330539)), 0, by norm_num⟩
  | 3 => ⟨((-39511662781/1125899906842624), (63535469681/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((27097345547/18014398509481984), (-86754178353/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-2711299723/144115188075855872), (110273478451/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-13616571575/2305843009213693952), (-65661906959/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((36024494501/36893488147419103232), (9132753085/4611686018427387904)), (5/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-32314756309/295147905179352825856), (-18733569655/147573952589676412928)), (9/295147905179352825856), by norm_num⟩
  | 9 => ⟨((24709229641/2361183241434822606848), (1069023687/147573952589676412928)), (7/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-34268839831/37778931862957161709568), (-12582137823/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((88263444667/1208925819614629174706176), (8701592787/1208925819614629174706176)), (33/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-106441498727/19342813113834066795298816), (8334525715/9671406556917033397649408)), (25/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (423/256)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (423/256)))⁻¹=value ((139264/947451), (-12032/315817)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((139264/947451), (-12032/315817))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-66662705871/281474976710656), (-19801273967/281474976710656)), (1/70368744177664), by norm_num⟩
  | 1 => ⟨((105739521149/562949953421312), (-29375906657/562949953421312)), (7/562949953421312), by norm_num⟩
  | 2 => ⟨((-8370046555/140737488355328), (38677555441/562949953421312)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((3670108065/1125899906842624), (-36607661465/1125899906842624)), (9/2251799813685248), by norm_num⟩
  | 4 => ⟨((5825709667/1125899906842624), (77497894669/9007199254740992)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((-93674242467/36028797018963968), (-17620049823/18014398509481984)), (17/36028797018963968), by norm_num⟩
  | 6 => ⟨((48558362767/72057594037927936), (-17075962689/72057594037927936)), (25/144115188075855872), by norm_num⟩
  | 7 => ⟨((-48741286731/576460752303423488), (87912003059/576460752303423488)), (17/288230376151711744), by norm_num⟩
  | 8 => ⟨((-23245083377/2305843009213693952), (-91715002045/2305843009213693952)), (45/2305843009213693952), by norm_num⟩
  | 9 => ⟨((74474299317/9223372036854775808), (44742597157/9223372036854775808)), (59/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-75824103653/36893488147419103232), (5164684989/9223372036854775808)), (77/36893488147419103232), by norm_num⟩
  | 11 => ⟨((32281593261/147573952589676412928), (-3922885129/9223372036854775808)), (25/36893488147419103232), by norm_num⟩
  | 12 => ⟨((23133513153/590295810358705651712), (14738627037/147573952589676412928)), (33/147573952589676412928), by norm_num⟩
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
  | 0 => ⟨((59/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((483328/3743473), (-108288/3743473)), 0, by norm_num⟩
  | 1 => ⟨((-110939832320/14013590101729), (52338622464/14013590101729)), 0, by norm_num⟩
  | 2 => ⟨((32161670385/70368744177664), (-25023783113/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-27428776215/1125899906842624), (33289767031/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((41254581543/36028797018963968), (-40732408303/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-742481135/18014398509481984), (93691826829/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((178695153/576460752303423488), (-51136194423/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((10357204135/73786976294838206464), (106298547489/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-22997586071/1180591620717411303424), (-13125229571/295147905179352825856)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((35903764701/18889465931478580854784), (48906031873/18889465931478580854784)), (11/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-6050325771/37778931862957161709568), (-21103085505/151115727451828646838272)), (15/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29881082813/2417851639229258349412352), (32393454539/4835703278458516698824704)), (5/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-17306148805/19342813113834066795298816), (-19629126651/77371252455336267181195264)), (13/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (423/256)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (423/256)))⁻¹=value ((483328/3743473), (-108288/3743473)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((483328/3743473), (-108288/3743473))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-73438099131/2251799813685248), (-314111929/140737488355328)), (3/1125899906842624), by norm_num⟩
  | 1 => ⟨((56023567847/2251799813685248), (-14071927009/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-4006269309/562949953421312), (3309509915/281474976710656)), (7/4503599627370496), by norm_num⟩
  | 3 => ⟨((-518621473/2251799813685248), (-46425177839/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 4 => ⟨((36258195767/36028797018963968), (23249554657/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((-8063556565/18014398509481984), (-17270302219/144115188075855872)), (15/144115188075855872), by norm_num⟩
  | 6 => ⟨((63860957925/576460752303423488), (-3518429691/72057594037927936)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((-14931104525/1152921504606846976), (484412629/18014398509481984)), (7/576460752303423488), by norm_num⟩
  | 8 => ⟨((-4623300795/2305843009213693952), (-31207627967/4611686018427387904)), (19/4611686018427387904), by norm_num⟩
  | 9 => ⟨((52025649521/36893488147419103232), (29537172023/36893488147419103232)), (49/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-51912014267/147573952589676412928), (7412685295/73786976294838206464)), (63/147573952589676412928), by norm_num⟩
  | 11 => ⟨((10978220439/295147905179352825856), (-85964739605/1180591620717411303424)), (41/295147905179352825856), by norm_num⟩
  | 12 => ⟨((15585843975/2361183241434822606848), (80279213645/4722366482869645213696)), (215/4722366482869645213696), by norm_num⟩
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
  | 0 => ⟨((67/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((548864/4775665), (-108288/4775665)), 0, by norm_num⟩
  | 1 => ⟨((-144762699776/22806976192225), (59435384832/22806976192225)), 0, by norm_num⟩
  | 2 => ⟨((11793793105/35184372088832), (-7800949189/35184372088832)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-37714131275/2251799813685248), (37247412913/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((3489876509/4503599627370496), (-41087893541/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-36432755903/1152921504606846976), (85684266647/1152921504606846976)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((8977221199/9223372036854775808), (-42694987693/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-1018224549/295147905179352825856), (81767434037/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-13896393651/4722366482869645213696), (-75364519773/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1652995271/4722366482869645213696), (33385975863/37778931862957161709568)), (1/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-36429547971/1208925819614629174706176), (-14148700833/302231454903657293676544)), (19/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((43760867617/19342813113834066795298816), (45426917081/19342813113834066795298816)), (11/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-48475686365/309485009821345068724781056), (-33828876329/309485009821345068724781056)), (25/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (423/256)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (423/256)))⁻¹=value ((548864/4775665), (-108288/4775665)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((548864/4775665), (-108288/4775665))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-68433211597/18014398509481984), (8700759709/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 1 => ⟨((12559643119/4503599627370496), (-9328734425/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 2 => ⟨((-12395145483/18014398509481984), (59927676317/36028797018963968)), (5/18014398509481984), by norm_num⟩
  | 3 => ⟨((-17677183057/144115188075855872), (-49758174037/72057594037927936)), (19/144115188075855872), by norm_num⟩
  | 4 => ⟨((46060120839/288230376151711744), (23606093719/144115188075855872)), (7/144115188075855872), by norm_num⟩
  | 5 => ⟨((-75172521775/1152921504606846976), (-12940411475/1152921504606846976)), (21/1152921504606846976), by norm_num⟩
  | 6 => ⟨((35737972963/2305843009213693952), (-37898687737/4611686018427387904)), (15/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-30919361487/18446744073709551616), (74379142839/18446744073709551616)), (39/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-24591402879/73786976294838206464), (-72530971021/73786976294838206464)), (53/73786976294838206464), by norm_num⟩
  | 9 => ⟨((31067019791/147573952589676412928), (33276719553/295147905179352825856)), (17/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-60831532857/1180591620717411303424), (9108306193/590295810358705651712)), (87/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((12773529623/2361183241434822606848), (-6306040401/590295810358705651712)), (57/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((36054180971/37778931862957161709568), (93666041959/37778931862957161709568)), (37/4722366482869645213696), by norm_num⟩
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
  | 0 => ⟨((75/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((204800/1979643), (-12032/659881)), 0, by norm_num⟩
  | 1 => ⟨((-20320059392/3918986407449), (2464153600/1306328802483)), 0, by norm_num⟩
  | 2 => ⟨((1947354949222400/7758194008601560707), (-124858268647424/862021556511284523)), 0, by norm_num⟩
  | 3 => ⟨((-13131554919/1125899906842624), (11012001759/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((37046731871/72057594037927936), (-44117119163/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-48450910827/2305843009213693952), (41916344869/1152921504606846976)), (5/2305843009213693952), by norm_num⟩
  | 6 => ⟨((27870567647/36893488147419103232), (-19112354031/9223372036854775808)), (3/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-1489346377/73786976294838206464), (16834203371/147573952589676412928)), (7/590295810358705651712), by norm_num⟩
  | 8 => ⟨((38614981/9444732965739290427392), (-114935106793/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((16701520097/302231454903657293676544), (743236835/2361183241434822606848)), (1/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-27699699575/4835703278458516698824704), (-76299209981/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((34054603811/77371252455336267181195264), (29553267631/38685626227668133590597632)), (17/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-18403100675/618970019642690137449562112), (-43950483769/1237940039285380274899124224)), (17/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (423/256)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (423/256)))⁻¹=value ((204800/1979643), (-12032/659881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((204800/1979643), (-12032/659881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-27683898789/72057594037927936), (1073951413/9007199254740992)), (1/18014398509481984), by norm_num⟩
  | 1 => ⟨((38842890807/144115188075855872), (-19802289107/72057594037927936)), (9/144115188075855872), by norm_num⟩
  | 2 => ⟨((-7535872545/144115188075855872), (29009583603/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 3 => ⟨((-28143744327/1152921504606846976), (-92337704423/1152921504606846976)), (11/576460752303423488), by norm_num⟩
  | 4 => ⟨((24801222125/1152921504606846976), (10348664405/576460752303423488)), (17/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-18968692929/2305843009213693952), (-1625104059/2305843009213693952)), (25/9223372036854775808), by norm_num⟩
  | 6 => ⟨((17390742433/9223372036854775808), (-43213931487/36893488147419103232)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-27557119037/147573952589676412928), (38773058085/73786976294838206464)), (47/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-28058589947/590295810358705651712), (-73490940243/590295810358705651712)), (63/590295810358705651712), by norm_num⟩
  | 9 => ⟨((32381575517/1180591620717411303424), (32659695901/2361183241434822606848)), (41/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-62279291841/9444732965739290427392), (4888541491/2361183241434822606848)), (13/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((25957399421/37778931862957161709568), (-25897891429/18889465931478580854784)), (17/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((36538459921/302231454903657293676544), (95587986263/302231454903657293676544)), (351/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((83/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((679936/7233265), (-108288/7233265)), 0, by norm_num⟩
  | 1 => ⟨((-225293336576/52320122560225), (73628909568/52320122560225)), 0, by norm_num⟩
  | 2 => ⟨((54001887921/281474976710656), (-6922562033/70368744177664)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-74587188111/9007199254740992), (54581941611/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((49553218407/144115188075855872), (-6247403417/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-31278673231/2305843009213693952), (43519704955/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((36619333929/73786976294838206464), (-72946795839/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-1175094567/73786976294838206464), (14810624803/295147905179352825856)), (1/147573952589676412928), by norm_num⟩
  | 8 => ⟨((7043650509/18889465931478580854784), (-93605498909/37778931862957161709568)), (15/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((617026099/604462909807314587353088), (36039732629/302231454903657293676544)), (7/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-18193453477/19342813113834066795298816), (-108261166745/19342813113834066795298816)), (25/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((26647738423/309485009821345068724781056), (79234516619/309485009821345068724781056)), (23/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-29529020721/4951760157141521099596496896), (-56393642421/4951760157141521099596496896)), (21/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (423/256)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (423/256)))⁻¹=value ((679936/7233265), (-108288/7233265)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((679936/7233265), (-108288/7233265))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19789581609/576460752303423488), (9776586209/576460752303423488)), (15/2305843009213693952), by norm_num⟩
  | 1 => ⟨((1636301137/72057594037927936), (-35650402239/1152921504606846976)), (17/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-1578163871/576460752303423488), (49179220889/2305843009213693952)), (23/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-16254534967/4611686018427387904), (-37751514151/4611686018427387904)), (23/9223372036854775808), by norm_num⟩
  | 4 => ⟨((23222736665/9223372036854775808), (31799171247/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-67521110157/73786976294838206464), (-777559137/147573952589676412928)), (13/36893488147419103232), by norm_num⟩
  | 6 => ⟨((29921121709/147573952589676412928), (-42777238521/295147905179352825856)), (19/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-10702730767/590295810358705651712), (35724943951/590295810358705651712)), (25/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-7004288587/1180591620717411303424), (-65979115939/4722366482869645213696)), (33/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((29928451731/9444732965739290427392), (28369312651/18889465931478580854784)), (43/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-56595389179/75557863725914323419136), (9311312771/37778931862957161709568)), (109/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((5849825083/75557863725914323419136), (-47255441119/302231454903657293676544)), (143/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((16478550923/1208925819614629174706176), (43338274377/1208925819614629174706176)), (183/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((91/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((745472/8658673), (-108288/8658673)), 0, by norm_num⟩
  | 1 => ⟨((-272001105920/74972618120929), (80725671936/74972618120929)), 0, by norm_num⟩
  | 2 => ⟨((42064842087/281474976710656), (-19432317775/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-27028506685/4503599627370496), (17592872641/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((67424273231/288230376151711744), (-59286153933/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-40507757969/4611686018427387904), (47579953597/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((5784965279/18446744073709551616), (-36824143619/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-24507230023/2361183241434822606848), (55356542089/2361183241434822606848)), (3/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((22682467949/75557863725914323419136), (-40579512421/37778931862957161709568)), (11/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-15005710487/2417851639229258349412352), (58168746787/1208925819614629174706176)), (19/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-652117245/19342813113834066795298816), (-20407580327/9671406556917033397649408)), (1/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((9065457977/618970019642690137449562112), (112186956947/1237940039285380274899124224)), (27/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-11856131475/9903520314283042199192993792), (-37728125103/9903520314283042199192993792)), (11/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (423/256)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (423/256)))⁻¹=value ((745472/8658673), (-108288/8658673)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((745472/8658673), (-108288/8658673))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-25304370799/9223372036854775808), (17427419629/9223372036854775808)), (13/18446744073709551616), by norm_num⟩
  | 1 => ⟨((15445866691/9223372036854775808), (-28082532661/9223372036854775808)), (15/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-101533091/4611686018427387904), (37115373191/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-30803584445/73786976294838206464), (-27576125827/36893488147419103232)), (21/73786976294838206464), by norm_num⟩
  | 4 => ⟨((38513255453/147573952589676412928), (43236656649/295147905179352825856)), (33/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-107434637099/1180591620717411303424), (7457157341/1180591620717411303424)), (3/73786976294838206464), by norm_num⟩
  | 6 => ⟨((46093626053/2361183241434822606848), (-37436270807/2361183241434822606848)), (35/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-1824402993/1180591620717411303424), (29476394369/4722366482869645213696)), (47/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-12429912895/18889465931478580854784), (-26578528669/18889465931478580854784)), (31/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((49675829573/151115727451828646838272), (5520594931/37778931862957161709568)), (5/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-92447367447/1208925819614629174706176), (31858225897/1208925819614629174706176)), (203/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((18949516677/2417851639229258349412352), (-77575889283/4835703278458516698824704)), (265/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((26786177665/19342813113834066795298816), (70708061129/19342813113834066795298816)), (85/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((99/8), (423/256)), 0, by norm_num⟩
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
  | 0 => ⟨((90112/1135017), (-12032/1135017)), 0, by norm_num⟩
  | 1 => ⟨((-1329233920/429421196763), (1084227584/1288263590289)), 0, by norm_num⟩
  | 2 => ⟨((173147177353216/1462201075459049913), (-72840971812864/1462201075459049913)), 0, by norm_num⟩
  | 3 => ⟨((-79922942979/18014398509481984), (46930309955/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((23391194135/144115188075855872), (-285822643/2251799813685248)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-53221550163/9223372036854775808), (54408490395/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((58378084161/295147905179352825856), (-39070566013/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-30451503859/4722366482869645213696), (27290723567/2361183241434822606848)), (3/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((29424362015/151115727451828646838272), (-74498772915/151115727451828646838272)), (5/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-24741393289/4835703278458516698824704), (49812592049/2417851639229258349412352)), (15/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((7265485659/77371252455336267181195264), (-65374266877/77371252455336267181195264)), (3/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((1859013359/2475880078570760549798248448), (84276084115/2475880078570760549798248448)), (9/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-16655669557/79228162514264337593543950336), (-53369553711/39614081257132168796771975168)), (27/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (423/256)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (423/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (423/256)))⁻¹=value ((90112/1135017), (-12032/1135017)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((90112/1135017), (-12032/1135017))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7296950613/36893488147419103232), (26429656325/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 1 => ⟨((31752101185/295147905179352825856), (-78992815145/295147905179352825856)), (23/295147905179352825856), by norm_num⟩
  | 2 => ⟨((308596393/18446744073709551616), (50519907999/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-50338811297/1180591620717411303424), (-36375709989/590295810358705651712)), (17/590295810358705651712), by norm_num⟩
  | 4 => ⟨((57357173749/2361183241434822606848), (3271423289/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-77266095161/9444732965739290427392), (1363481167/1180591620717411303424)), (5/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((16059937467/9444732965739290427392), (-58742802487/37778931862957161709568)), (29/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-2186984395/18889465931478580854784), (88051670687/151115727451828646838272)), (39/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-4960472857/75557863725914323419136), (-77660202683/604462909807314587353088)), (13/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((74795462937/2417851639229258349412352), (3889400659/302231454903657293676544)), (67/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-4284466985/604462909807314587353088), (12359838083/4835703278458516698824704)), (171/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((27853224145/38685626227668133590597632), (-57864207469/38685626227668133590597632)), (221/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((19813578375/154742504910672534362390528), (1638015307/4835703278458516698824704)), (71/38685626227668133590597632), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((76999110273/274877906944), (28080255693/274877906944)), (887/274877906944), by norm_num⟩
  | 1 => ⟨((8776516285/274877906944), (100042734565/549755813888)), (131/17179869184), by norm_num⟩
  | 2 => ⟨((-31468537707/1099511627776), (12950573631/549755813888)), (9979/1099511627776), by norm_num⟩
  | 3 => ⟨((18162391321/17592186044416), (32706402363/17592186044416)), (133495/17592186044416), by norm_num⟩
  | 4 => ⟨((-7308319129/8796093022208), (34761580703/17592186044416)), (175763/35184372088832), by norm_num⟩
  | 5 => ⟨((-89727823273/281474976710656), (-5690458193/35184372088832)), (763863/281474976710656), by norm_num⟩
  | 6 => ⟨((8520584827/140737488355328), (6030737893/562949953421312)), (1416739/1125899906842624), by norm_num⟩
  | 7 => ⟨((-64722346425/4503599627370496), (61582755611/4503599627370496)), (72103/140737488355328), by norm_num⟩
  | 8 => ⟨((-10007088151/18014398509481984), (-1159822599/281474976710656)), (843911/4503599627370496), by norm_num⟩
  | 9 => ⟨((54719060731/72057594037927936), (20795473089/36028797018963968)), (4517829/72057594037927936), by norm_num⟩
  | 10 => ⟨((-31692678861/144115188075855872), (7273882023/144115188075855872)), (2807043/144115188075855872), by norm_num⟩
  | 11 => ⟨((13535173265/576460752303423488), (-52859938363/1152921504606846976)), (6556037/1152921504606846976), by norm_num⟩
  | 12 => ⟨((10536297723/2305843009213693952), (25317654483/2305843009213693952)), (7271635/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((76999110273/274877906944), (28080255693/274877906944)), (111/34359738368), by norm_num⟩
  | 1 => ⟨((8776516285/274877906944), (100042734565/549755813888)), (4193/549755813888), by norm_num⟩
  | 2 => ⟨((-31468537707/1099511627776), (12950573631/549755813888)), (19959/2199023255552), by norm_num⟩
  | 3 => ⟨((18162391321/17592186044416), (32706402363/17592186044416)), (16687/2199023255552), by norm_num⟩
  | 4 => ⟨((-7308319129/8796093022208), (34761580703/17592186044416)), (175765/35184372088832), by norm_num⟩
  | 5 => ⟨((-89727823273/281474976710656), (-5690458193/35184372088832)), (763875/281474976710656), by norm_num⟩
  | 6 => ⟨((8520584827/140737488355328), (6030737893/562949953421312)), (1416785/1125899906842624), by norm_num⟩
  | 7 => ⟨((-64722346425/4503599627370496), (61582755611/4503599627370496)), (2307477/4503599627370496), by norm_num⟩
  | 8 => ⟨((-10007088151/18014398509481984), (-1159822599/281474976710656)), (3376365/18014398509481984), by norm_num⟩
  | 9 => ⟨((54719060731/72057594037927936), (20795473089/36028797018963968)), (565089/9007199254740992), by norm_num⟩
  | 10 => ⟨((-31692678861/144115188075855872), (7273882023/144115188075855872)), (351601/18014398509481984), by norm_num⟩
  | 11 => ⟨((13535173265/576460752303423488), (-52859938363/1152921504606846976)), (3301077/576460752303423488), by norm_num⟩
  | 12 => ⟨((10536297723/2305843009213693952), (25317654483/2305843009213693952)), (7456103/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile007Gamma
