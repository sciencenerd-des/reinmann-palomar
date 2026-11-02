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
namespace Reinmann.XiRectangle.Tile010Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2961/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2961/640))
  have he : value ((3/4), (2961/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/301861921), (-3790080/301861921)), 0, by norm_num⟩
  | 1 => ⟨((-232920579276800/91120619349810241), (83054297088000/91120619349810241)), 0, by norm_num⟩
  | 2 => ⟨((49010711621/562949953421312), (-27658569567/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-51370397995/18014398509481984), (20985842675/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((51235839491/576460752303423488), (-59070644667/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-47644524111/18446744073709551616), (78904336371/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((19744373027/295147905179352825856), (-50610017113/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-1595791071/1180591620717411303424), (62750832323/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((2222236869/302231454903657293676544), (-18862691141/75557863725914323419136)), (3/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((6288099489/4835703278458516698824704), (44041867205/4835703278458516698824704)), (17/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-16151336797/154742504910672534362390528), (-99784267769/309485009821345068724781056)), (3/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((28782914309/4951760157141521099596496896), (27352940791/2475880078570760549798248448)), (17/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-44421737509/158456325028528675187087900672), (-28879780667/79228162514264337593543950336)), (3/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (2961/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (2961/1280)))⁻¹=value ((21913600/301861921), (-3790080/301861921)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/301861921), (-3790080/301861921))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44807242379/17179869184), (1471123681/8589934592)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((10956800/301861921), (-1895040/301861921)), 0, by norm_num⟩
  | 2 => ⟨((-58230144819200/91120619349810241), (20763574272000/91120619349810241)), 0, by norm_num⟩
  | 3 => ⟨((65347615495/4503599627370496), (-9219523189/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-51370397995/144115188075855872), (20985842675/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((40988671593/4611686018427387904), (-23628257867/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-15881508037/73786976294838206464), (26301445457/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((22564997745/4722366482869645213696), (-28920009779/2361183241434822606848)), (7/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-1595791071/18889465931478580854784), (62750832323/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1975321661/4835703278458516698824704), (-67067346279/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((5030479591/77371252455336267181195264), (8808373441/19342813113834066795298816)), (7/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-23492853523/4951760157141521099596496896), (-72570376559/4951760157141521099596496896)), (9/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((38377219079/158456325028528675187087900672), (72941175443/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (63/20480)), 0, by norm_num⟩
  | 45 => ⟨((105756830033/4080638361600), (-125181/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-50520294863959/1915179604377600), (874892421431/197568495616000)), 0, by norm_num⟩
  | 43 => ⟨((59249064809/2199023255552), (-2496099489/549755813888)), (1/2199023255552), by norm_num⟩
  | 42 => ⟨((-60634701219/2199023255552), (10204299709/2199023255552)), (1/1099511627776), by norm_num⟩
  | 41 => ⟨((31053627885/1099511627776), (-1305089095/274877906944)), (1/1099511627776), by norm_num⟩
  | 40 => ⟨((-15913883493/549755813888), (10692401329/2199023255552)), (1/1099511627776), by norm_num⟩
  | 39 => ⟨((510021793/17179869184), (-1369693021/274877906944)), (1/1099511627776), by norm_num⟩
  | 38 => ⟨((-33497624051/1099511627776), (11236312897/2199023255552)), (1/2199023255552), by norm_num⟩
  | 37 => ⟨((1074998779/34359738368), (-11529635789/2199023255552)), (1/2199023255552), by norm_num⟩
  | 36 => ⟨((-70704510857/2199023255552), (11838678949/2199023255552)), (1/1099511627776), by norm_num⟩
  | 35 => ⟨((36358778779/1099511627776), (-12164746969/2199023255552)), (1/1099511627776), by norm_num⟩
  | 34 => ⟨((-74848598795/2199023255552), (1563661119/274877906944)), (1/1099511627776), by norm_num⟩
  | 33 => ⟨((9638540327/274877906944), (-1609240185/274877906944)), (1/2199023255552), by norm_num⟩
  | 32 => ⟨((-39754374171/1099511627776), (13260455051/2199023255552)), (1/2199023255552), by norm_num⟩
  | 31 => ⟨((1282241257/34359738368), (-6835462227/1099511627776)), (1/2199023255552), by norm_num⟩
  | 30 => ⟨((-42393882529/1099511627776), (7053812337/1099511627776)), (1/2199023255552), by norm_num⟩
  | 29 => ⟨((43849599675/1099511627776), (-14573153869/2199023255552)), (1/2199023255552), by norm_num⟩
  | 28 => ⟨((-45408853505/1099511627776), (7535232575/1099511627776)), (1/2199023255552), by norm_num⟩
  | 27 => ⟨((94166196789/2199023255552), (-15602929363/2199023255552)), (1/2199023255552), by norm_num⟩
  | 26 => ⟨((-24442771609/549755813888), (16174411687/2199023255552)), (1/2199023255552), by norm_num⟩
  | 25 => ⟨((101663001385/2199023255552), (-16789365733/2199023255552)), (1/2199023255552), by norm_num⟩
  | 24 => ⟨((-105877647337/2199023255552), (8726474999/1099511627776)), (1/2199023255552), by norm_num⟩
  | 23 => ⟨((110456909405/2199023255552), (-18171173133/2199023255552)), (1/2199023255552), by norm_num⟩
  | 22 => ⟨((-115450249593/2199023255552), (18951076683/2199023255552)), (1/2199023255552), by norm_num⟩
  | 21 => ⟨((30229125387/549755813888), (-4950241781/549755813888)), (1/1099511627776), by norm_num⟩
  | 20 => ⟨((-31731550235/549755813888), (10365356705/1099511627776)), (1/549755813888), by norm_num⟩
  | 19 => ⟨((66782323879/1099511627776), (-5438033179/549755813888)), (1/549755813888), by norm_num⟩
  | 18 => ⟨((-70467991809/1099511627776), (11439748241/1099511627776)), (1/549755813888), by norm_num⟩
  | 17 => ⟨((74584349787/1099511627776), (-12065101457/1099511627776)), (1/1099511627776), by norm_num⟩
  | 16 => ⟨((-9901449789/137438953472), (12762841827/1099511627776)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((84451175365/1099511627776), (-6773161405/549755813888)), (1/549755813888), by norm_num⟩
  | 14 => ⟨((-90433287389/1099511627776), (7216200559/549755813888)), (1/1099511627776), by norm_num⟩
  | 13 => ⟨((24331972763/274877906944), (-3860666891/274877906944)), (1/1099511627776), by norm_num⟩
  | 12 => ⟨((-13170140503/137438953472), (16605236739/1099511627776)), (1/1099511627776), by norm_num⟩
  | 11 => ⟨((57420312755/549755813888), (-17957416195/1099511627776)), (1/1099511627776), by norm_num⟩
  | 10 => ⟨((-15774489783/137438953472), (9774902601/549755813888)), (1/549755813888), by norm_num⟩
  | 9 => ⟨((70022732059/549755813888), (-10726402819/549755813888)), (1/549755813888), by norm_num⟩
  | 8 => ⟨((-78656757057/549755813888), (5941846267/274877906944)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((89723023851/549755813888), (-13321868387/549755813888)), (1/549755813888), by norm_num⟩
  | 6 => ⟨((-52210037905/274877906944), (7578890415/274877906944)), (1/549755813888), by norm_num⟩
  | 5 => ⟨((15611383541/68719476736), (-2197985767/68719476736)), (1/274877906944), by norm_num⟩
  | 4 => ⟨((-77693307369/274877906944), (654425523/17179869184)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((51429328465/137438953472), (-12950771447/274877906944)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((-76220889163/137438953472), (4249012149/68719476736)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((37178824521/34359738368), (-6207114611/68719476736)), (1/68719476736), by norm_num⟩
  | 0 => ⟨((-22603753361/137438953472), (23537978897/137438953472)), (1/137438953472), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (2961/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (2961/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (2961/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((44807242379/17179869184), (1471123681/8589934592)), (1/34359738368), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (2961/1280))) (z:=((-21/128), (2961/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((44807242379/17179869184), (1471123681/8589934592))) (r:=(1/34359738368)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((71260874997/2147483648), (4422912139/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((7670440893/4294967296), (381262473/4294967296)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((855975246412800/91120619349810241), (-153391890828960/91120619349810241)), 0, by norm_num⟩
  | 3 => ⟨((-16010646457/140737488355328), (5921174527/140737488355328)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((35884457623/18014398509481984), (-42124553425/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-46219902343/1152921504606846976), (19742206373/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((3912019759/4611686018427387904), (-9519926297/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-41941839237/2361183241434822606848), (37288797251/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((12878289943/37778931862957161709568), (-73527727639/75557863725914323419136)), (59/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-5920839017/1208925819614629174706176), (72545354193/2417851639229258349412352)), (39/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-467491237/38685626227668133590597632), (-2227206997/2417851639229258349412352)), (203/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((13190274601/2475880078570760549798248448), (8673914043/309485009821345068724781056)), (125/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-6314051779/19807040628566084398385987584), (-1040867889/1237940039285380274899124224)), (41/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((42538281205/2147483648), (25447829797/4294967296)), (5/4294967296), by norm_num⟩
  | 1 => ⟨((5522957245/4294967296), (381262473/4294967296)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((855975246412800/91120619349810241), (-153391890828960/91120619349810241)), 0, by norm_num⟩
  | 3 => ⟨((-16010646457/140737488355328), (5921174527/140737488355328)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((35884457623/18014398509481984), (-42124553425/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-46219902343/1152921504606846976), (19742206373/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((3912019759/4611686018427387904), (-9519926297/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-41941839237/2361183241434822606848), (37288797251/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((12878289943/37778931862957161709568), (-73527727639/75557863725914323419136)), (59/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-5920839017/1208925819614629174706176), (72545354193/2417851639229258349412352)), (39/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-467491237/38685626227668133590597632), (-2227206997/2417851639229258349412352)), (203/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((13190274601/2475880078570760549798248448), (8673914043/309485009821345068724781056)), (125/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-6314051779/19807040628566084398385987584), (-1040867889/1237940039285380274899124224)), (41/9903520314283042199192993792), by norm_num⟩
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
  | 0 => ⟨((89023373357/4294967296), (25447829797/4294967296)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((5522957245/4294967296), (381262473/4294967296)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((855975246412800/91120619349810241), (-153391890828960/91120619349810241)), 0, by norm_num⟩
  | 3 => ⟨((-16010646457/140737488355328), (5921174527/140737488355328)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((35884457623/18014398509481984), (-42124553425/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-46219902343/1152921504606846976), (19742206373/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((3912019759/4611686018427387904), (-9519926297/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-41941839237/2361183241434822606848), (37288797251/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((12878289943/37778931862957161709568), (-73527727639/75557863725914323419136)), (59/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-5920839017/1208925819614629174706176), (72545354193/2417851639229258349412352)), (39/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-467491237/38685626227668133590597632), (-2227206997/2417851639229258349412352)), (203/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((13190274601/2475880078570760549798248448), (8673914043/309485009821345068724781056)), (125/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-6314051779/19807040628566084398385987584), (-1040867889/1237940039285380274899124224)), (41/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((465841158553600/91120619349810241), (-166108594176000/91120619349810241)), 0, by norm_num⟩
  | 1 => ⟨((-49010711621/140737488355328), (27658569567/140737488355328)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((1203993703/70368744177664), (-31478764013/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-51235839491/72057594037927936), (59070644667/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((29777827569/1152921504606846976), (-6164401279/144115188075855872)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((-29616559541/36893488147419103232), (75915025669/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 6 => ⟨((11170537497/590295810358705651712), (-27453489141/295147905179352825856)), (3/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-2222236869/18889465931478580854784), (18862691141/4722366482869645213696)), (5/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-7074111925/302231454903657293676544), (-99094201211/604462909807314587353088)), (1/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((5047292749/2417851639229258349412352), (62365167355/9671406556917033397649408)), (13/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-19788253587/154742504910672534362390528), (-75220587175/309485009821345068724781056)), (5/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((8329075783/1237940039285380274899124224), (5414958875/618970019642690137449562112)), (1/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-51349955097/158456325028528675187087900672), (-47258871703/158456325028528675187087900672)), (23/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((49010711621/140737488355328), (-27658569567/140737488355328)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-1203993703/35184372088832), (31478764013/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 2 => ⟨((19213439809/9007199254740992), (-44302983501/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 3 => ⟨((-29777827569/288230376151711744), (6164401279/36028797018963968)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((37020699425/9223372036854775808), (-94893782087/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-8377903123/73786976294838206464), (82360467423/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((3888914521/4722366482869645213696), (-66019418993/2361183241434822606848)), (17/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((7074111925/37778931862957161709568), (99094201211/75557863725914323419136)), (15/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-22712817371/1208925819614629174706176), (-70160813275/1208925819614629174706176)), (7/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((3091914623/2417851639229258349412352), (5876608373/2417851639229258349412352)), (3/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-22904958403/309485009821345068724781056), (-59564547625/618970019642690137449562112)), (19/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((19256233161/4951760157141521099596496896), (35444153777/9903520314283042199192993792)), (1/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-15123870101/79228162514264337593543950336), (-39004197631/316912650057057350374175801344)), (3/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((51370397995/2251799813685248), (-20985842675/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-25617919745/9007199254740992), (14767661167/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((29777827569/144115188075855872), (-6164401279/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((-24680466283/2305843009213693952), (63262521391/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 4 => ⟨((13963171871/36893488147419103232), (-68633722853/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-3888914521/1180591620717411303424), (132038837987/1180591620717411303424)), (15/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-16506261159/18889465931478580854784), (-28902475353/4722366482869645213696)), (17/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((15141878247/151115727451828646838272), (93547751033/302231454903657293676544)), (17/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-9275743869/1208925819614629174706176), (-17629825119/1208925819614629174706176)), (17/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((2385933167/4835703278458516698824704), (49637123021/77371252455336267181195264)), (1/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-35303094129/1237940039285380274899124224), (-64980948591/2475880078570760549798248448)), (13/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((15123870101/9903520314283042199192993792), (19502098815/19807040628566084398385987584)), (23/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-12203450371/158456325028528675187087900672), (-20719396231/633825300114114700748351602688)), (19/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((51235839491/36028797018963968), (-59070644667/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((-29777827569/144115188075855872), (6164401279/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((37020699425/2305843009213693952), (-94893782087/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 3 => ⟨((-13963171871/18446744073709551616), (68633722853/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((2430571575/295147905179352825856), (-41262136871/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 5 => ⟨((12379695869/4722366482869645213696), (86707426059/4722366482869645213696)), (13/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-26498286933/75557863725914323419136), (-81854282153/75557863725914323419136)), (15/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((9275743869/302231454903657293676544), (17629825119/302231454903657293676544)), (1/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-42946797005/19342813113834066795298816), (-27920881699/9671406556917033397649408)), (17/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((44128867661/309485009821345068724781056), (40613092869/309485009821345068724781056)), (17/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-83181285555/9903520314283042199192993792), (-26815385871/4951760157141521099596496896)), (31/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((36610351113/79228162514264337593543950336), (15539547173/79228162514264337593543950336)), (7/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-30430185713/1267650600228229401496703205376), (-14259677279/2535301200456458802993406410752)), (25/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((47644524111/576460752303423488), (-78904336371/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 1 => ⟨((-7404139885/576460752303423488), (75915025669/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((16755806245/18446744073709551616), (-82360467423/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-486114315/36893488147419103232), (132038837987/295147905179352825856)), (17/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-6189847935/1180591620717411303424), (-21676856515/590295810358705651712)), (7/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((3881585/4611686018427387904), (12278142323/4722366482869645213696)), (9/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-25972082833/302231454903657293676544), (-49363510333/302231454903657293676544)), (3/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((8589359401/1208925819614629174706176), (44673410719/4835703278458516698824704)), (7/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-39715980895/77371252455336267181195264), (-18275891791/38685626227668133590597632)), (15/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((83181285555/2475880078570760549798248448), (53630771741/2475880078570760549798248448)), (31/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-2516961639/1237940039285380274899124224), (-34187003781/39614081257132168796771975168)), (31/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((73032445711/633825300114114700748351602688), (17111612735/633825300114114700748351602688)), (15/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-62521718597/10141204801825835211973625643008), (-460759735/1267650600228229401496703205376)), (7/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19744373027/4611686018427387904), (-50610017113/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-11170537497/18446744073709551616), (27453489141/9223372036854775808)), (13/36893488147419103232), by norm_num⟩
  | 2 => ⟨((486114315/36893488147419103232), (-66019418993/147573952589676412928)), (17/295147905179352825856), by norm_num⟩
  | 3 => ⟨((2063282645/295147905179352825856), (28902475353/590295810358705651712)), (9/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-13249143467/9444732965739290427392), (-40927141077/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((12986041417/75557863725914323419136), (49363510333/151115727451828646838272)), (3/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-40083677205/2417851639229258349412352), (-13029744793/604462909807314587353088)), (17/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((52954641193/38685626227668133590597632), (48735711443/38685626227668133590597632)), (21/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-31192982083/309485009821345068724781056), (-20111539403/309485009821345068724781056)), (3/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((4194936065/618970019642690137449562112), (28489169817/9903520314283042199192993792)), (27/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-8368301071/19807040628566084398385987584), (-15685645007/158456325028528675187087900672)), (7/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((62521718597/2535301200456458802993406410752), (460759735/316912650057057350374175801344)), (57/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((-55020379839/40564819207303340847894502572032), (12417895849/81129638414606681695789005144064)), (7/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1595791071/9223372036854775808), (-62750832323/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-2222236869/295147905179352825856), (18862691141/73786976294838206464)), (11/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-14148223851/2361183241434822606848), (-49547100605/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 3 => ⟨((30283756495/18889465931478580854784), (11693468879/2361183241434822606848)), (9/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-37102975477/151115727451828646838272), (-17629825119/37778931862957161709568)), (9/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((34357437605/1208925819614629174706176), (22336705359/604462909807314587353088)), (15/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-26477320597/9671406556917033397649408), (-48735711443/19342813113834066795298816)), (21/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((35649122381/154742504910672534362390528), (45969232921/309485009821345068724781056)), (29/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-86295827623/4951760157141521099596496896), (-18314466311/2475880078570760549798248448)), (9/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((47818863263/39614081257132168796771975168), (22408064295/79228162514264337593543950336)), (21/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-49124207469/633825300114114700748351602688), (-5792408097/1267650600228229401496703205376)), (23/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((94320651153/20282409603651670423947251286016), (-10643910727/20282409603651670423947251286016)), (25/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-21259560819/81129638414606681695789005144064), (24788055545/324518553658426726783156020576256)), (51/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2222236869/1180591620717411303424), (-18862691141/295147905179352825856)), (3/295147905179352825856), by norm_num⟩
  | 1 => ⟨((14148223851/4722366482869645213696), (99094201211/4722366482869645213696)), (9/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((-22712817371/18889465931478580854784), (-35080406637/9444732965739290427392)), (15/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((37102975477/151115727451828646838272), (17629825119/37778931862957161709568)), (9/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-21473398503/604462909807314587353088), (-27920881699/604462909807314587353088)), (9/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((1241124403/302231454903657293676544), (18275891791/4835703278458516698824704)), (17/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((-62385964167/154742504910672534362390528), (-20111539403/77371252455336267181195264)), (13/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((10786978453/309485009821345068724781056), (18314466311/1237940039285380274899124224)), (37/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((-53796221171/19807040628566084398385987584), (-6302268083/9903520314283042199192993792)), (49/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((122810518673/633825300114114700748351602688), (7240510121/633825300114114700748351602688)), (61/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-64845447667/5070602400912917605986812821504), (7317688625/5070602400912917605986812821504)), (9/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((63778682457/81129638414606681695789005144064), (-18591041659/81129638414606681695789005144064)), (5/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-29310509395/649037107316853453566312041152512), (28671959557/1298074214633706907132624082305024)), (43/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6288099489/9444732965739290427392), (-44041867205/9444732965739290427392)), (17/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((20189170997/37778931862957161709568), (62365167355/37778931862957161709568)), (15/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-3091914623/18889465931478580854784), (-5876608373/18889465931478580854784)), (13/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((2385933167/75557863725914323419136), (49637123021/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((-22064433831/4835703278458516698824704), (-40613092869/9671406556917033397649408)), (19/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((83181285557/154742504910672534362390528), (53630771741/154742504910672534362390528)), (9/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-67118977041/1237940039285380274899124224), (-28489169817/1237940039285380274899124224)), (15/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((95637726527/19807040628566084398385987584), (22408064295/19807040628566084398385987584)), (45/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((-122810518673/316912650057057350374175801344), (-7240510121/316912650057057350374175801344)), (63/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((72050497409/2535301200456458802993406410752), (-8130765139/2535301200456458802993406410752)), (21/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-77951723003/40564819207303340847894502572032), (11361192125/20282409603651670423947251286016)), (13/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((39080679193/324518553658426726783156020576256), (-38229279409/649037107316853453566312041152512)), (61/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-72717572157/10384593717069655257060992658440192), (52592606201/10384593717069655257060992658440192)), (69/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-16151336797/151115727451828646838272), (-99784267769/302231454903657293676544)), (3/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((39576507175/604462909807314587353088), (75220587175/604462909807314587353088)), (3/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((-22904958403/1208925819614629174706176), (-59564547625/2417851639229258349412352)), (11/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((70606188259/19342813113834066795298816), (64980948591/19342813113834066795298816)), (31/19342813113834066795298816), by norm_num⟩
  | 4 => ⟨((-20795321389/38685626227668133590597632), (-53630771741/154742504910672534362390528)), (37/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((40271386225/618970019642690137449562112), (8546750945/309485009821345068724781056)), (37/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-66946408569/9903520314283042199192993792), (-7842822503/4951760157141521099596496896)), (33/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((98248414939/158456325028528675187087900672), (181012753/4951760157141521099596496896)), (53/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((-16211361917/316912650057057350374175801344), (3658844313/633825300114114700748351602688)), (39/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((19487930751/5070602400912917605986812821504), (-11361192125/10141204801825835211973625643008)), (27/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((-85977494225/324518553658426726783156020576256), (42052207351/324518553658426726783156020576256)), (71/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((21815271647/1298074214633706907132624082305024), (-31555563721/2596148429267413814265248164610048)), (11/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-20321754525/20769187434139310514121985316880384), (2602031785/2596148429267413814265248164610048)), (13/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/905585763), (-315840/301861921)), 0, by norm_num⟩
  | 1 => ⟨((-58230144819200/273361858049430723), (6921191424000/91120619349810241)), 0, by norm_num⟩
  | 2 => ⟨((65347615495/9007199254740992), (-9219523189/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-68493863993/288230376151711744), (55962247133/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((34157226327/4611686018427387904), (-19690214889/2305843009213693952)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-15881508037/73786976294838206464), (26301445457/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 6 => ⟨((26325830703/4722366482869645213696), (-67480022817/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-531930357/4722366482869645213696), (83667776431/151115727451828646838272)), (11/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((740745623/1208925819614629174706176), (-100601019419/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((2096033163/19342813113834066795298816), (117444979213/154742504910672534362390528)), (23/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((-21535115729/2475880078570760549798248448), (-66522845179/2475880078570760549798248448)), (17/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((38377219079/79228162514264337593543950336), (72941175443/79228162514264337593543950336)), (3/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-59228983345/2535301200456458802993406410752), (-77012748445/2535301200456458802993406410752)), (33/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89049356041/4294967296), (12721667973/2147483648)), (7/4294967296), by norm_num⟩
  | 1 => ⟨((88352677649/68719476736), (3052709625/34359738368)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((41346584901/4398046511104), (-14843302719/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-32088181453/281474976710656), (5948499843/140737488355328)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((72035768577/36028797018963968), (-42432213033/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-23234025453/576460752303423488), (39895372831/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1968864289/2305843009213693952), (-19303446433/18446744073709551616)), (33/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-41218559/2305843009213693952), (75884903509/2361183241434822606848)), (87/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((25802876487/75557863725914323419136), (-75099618567/75557863725914323419136)), (15/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-11579673889/2417851639229258349412352), (74380431993/2417851639229258349412352)), (157/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-1607954841/77371252455336267181195264), (-2292170713/2417851639229258349412352)), (205/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((14389562697/2475880078570760549798248448), (71670724077/2475880078570760549798248448)), (63/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-13553556423/39614081257132168796771975168), (-69022193285/79228162514264337593543950336)), (165/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-34852061597/36028797018963968), (39336632273/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 1 => ⟨((27397545597/288230376151711744), (-44769797707/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((-54651562123/9223372036854775808), (31504343823/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 3 => ⟨((21175344049/73786976294838206464), (-35068593943/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-13162915351/1180591620717411303424), (67480022817/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((11915239997/37778931862957161709568), (-58567443501/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-1382725163/604462909807314587353088), (46947142395/604462909807314587353088)), (13/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-5030479591/9671406556917033397649408), (-8808373441/2417851639229258349412352)), (3/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((16151336797/309485009821345068724781056), (99784267769/618970019642690137449562112)), (21/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-2198694843/618970019642690137449562112), (-66862744155/9903520314283042199192993792)), (9/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((4071992605/19807040628566084398385987584), (10589252911/39614081257132168796771975168)), (15/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-13693321359/1267650600228229401496703205376), (-25204731575/2535301200456458802993406410752)), (3/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((43019008287/81129638414606681695789005144064), (27736318315/81129638414606681695789005144064)), (9/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44524675943/2147483648), (25443338291/4294967296)), (1/536870912), by norm_num⟩
  | 1 => ⟨((88352684181/68719476736), (6105413913/68719476736)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((41346558841/4398046511104), (-14843242629/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-64176201351/562949953421312), (5948432955/140737488355328)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((72035366877/36028797018963968), (-21215591685/18014398509481984)), (19/36028797018963968), by norm_num⟩
  | 5 => ⟨((-23233843641/576460752303423488), (19946792747/576460752303423488)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((31501744229/36893488147419103232), (-2412751715/2305843009213693952)), (17/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-2638064535/147573952589676412928), (37938150791/1180591620717411303424)), (11/295147905179352825856), by norm_num⟩
  | 8 => ⟨((6451704921/18889465931478580854784), (-37543718935/37778931862957161709568)), (121/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-11588262541/2417851639229258349412352), (74364108081/2417851639229258349412352)), (79/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-398012155/19342813113834066795298816), (-73328780681/77371252455336267181195264)), (103/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((14362817929/2475880078570760549798248448), (71646110081/2475880078570760549798248448)), (253/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-1691568881/4951760157141521099596496896), (-68995107037/79228162514264337593543950336)), (331/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10409821357/9223372036854775808), (-24003309579/18446744073709551616)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-24200393199/147573952589676412928), (80156786155/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 2 => ⟨((7521665915/590295810358705651712), (-77120026077/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-177310119/295147905179352825856), (13944629405/4722366482869645213696)), (7/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((1975321661/302231454903657293676544), (-67067346279/302231454903657293676544)), (9/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((5030479591/2417851639229258349412352), (70466987527/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-10767557865/38685626227668133590597632), (-33261422589/38685626227668133590597632)), (13/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((7538382319/309485009821345068724781056), (57310923561/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-8725698439/4951760157141521099596496896), (-11345628119/4951760157141521099596496896)), (15/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((17931730351/158456325028528675187087900672), (33006196109/316912650057057350374175801344)), (15/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-67601298737/10141204801825835211973625643008), (-43585643067/10141204801825835211973625643008)), (13/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((14876587119/40564819207303340847894502572032), (25257930643/162259276829213363391578010288128)), (3/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-24730563627/1298074214633706907132624082305024), (-5794408545/1298074214633706907132624082305024)), (21/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89049351891/4294967296), (25443338285/4294967296)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((44176342085/34359738368), (1526353483/17179869184)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((41346558897/4398046511104), (-3710810729/2199023255552)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-64176201689/562949953421312), (11896866741/281474976710656)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((9004420889/4503599627370496), (-42431191365/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-46467684883/1152921504606846976), (39893602295/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 6 => ⟨((3937716745/4611686018427387904), (-38604059161/36893488147419103232)), (35/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-42208975047/2361183241434822606848), (37938205447/1180591620717411303424)), (89/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((6451671635/18889465931478580854784), (-75087610991/75557863725914323419136)), (61/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-11587988925/2417851639229258349412352), (37182179949/1208925819614629174706176)), (159/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-1592564377/77371252455336267181195264), (-73329113213/77371252455336267181195264)), (207/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((3590931481/618970019642690137449562112), (35823247743/1237940039285380274899124224)), (127/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-13533305765/39614081257132168796771975168), (-17248865175/19807040628566084398385987584)), (83/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1504333183/590295810358705651712), (30848010431/4722366482869645213696)), (7/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((13617417139/37778931862957161709568), (-8366777643/4722366482869645213696)), (9/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-2370385993/302231454903657293676544), (40240407767/151115727451828646838272)), (11/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-10060959183/2417851639229258349412352), (-70466987527/2417851639229258349412352)), (3/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((8075668399/9671406556917033397649408), (99784267769/38685626227668133590597632)), (21/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-7915301435/77371252455336267181195264), (-60176469739/309485009821345068724781056)), (1/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((48863911259/4951760157141521099596496896), (63535517467/4951760157141521099596496896)), (11/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((-4034639329/4951760157141521099596496896), (-59411152997/79228162514264337593543950336)), (13/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((76051461079/1267650600228229401496703205376), (49033848449/1267650600228229401496703205376)), (15/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((-40910614577/10141204801825835211973625643008), (-17364827317/10141204801825835211973625643008)), (17/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((81610859969/324518553658426726783156020576256), (19121548199/324518553658426726783156020576256)), (35/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-38108476097/2596148429267413814265248164610048), (-4493504463/5192296858534827628530496329220096)), (9/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((33536231521/41538374868278621028243970633760768), (-473062699/5192296858534827628530496329220096)), (35/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89049351891/4294967296), (25443338285/4294967296)), (5/2147483648), by norm_num⟩
  | 1 => ⟨((44176342085/34359738368), (1526353483/17179869184)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((41346558897/4398046511104), (-7421621457/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-64176201691/562949953421312), (11896866733/281474976710656)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((36017683571/18014398509481984), (-5303898909/4503599627370496)), (21/36028797018963968), by norm_num⟩
  | 5 => ⟨((-46467685001/1152921504606846976), (39893602071/1152921504606846976)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((7875433581/9223372036854775808), (-603188417/576460752303423488)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-42208976971/2361183241434822606848), (75876409123/2361183241434822606848)), (45/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((25806691073/75557863725914323419136), (-18771902017/18889465931478580854784)), (123/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-11587998679/2417851639229258349412352), (37182177879/1208925819614629174706176)), (5/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-1592544919/77371252455336267181195264), (-36664554327/38685626227668133590597632)), (13/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((14363689581/2475880078570760549798248448), (71646493343/2475880078570760549798248448)), (255/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-27066547565/79228162514264337593543950336), (-34497733959/39614081257132168796771975168)), (333/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1915463429/1208925819614629174706176), (-130070004905/2417851639229258349412352)), (11/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((1524387755/604462909807314587353088), (85414530337/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 2 => ⟨((-1223586121/1208925819614629174706176), (-30237656899/9671406556917033397649408)), (7/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((31981015899/154742504910672534362390528), (15196078217/38685626227668133590597632)), (17/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((-37018114591/1237940039285380274899124224), (-48132967777/1237940039285380274899124224)), (1/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((68466606797/19807040628566084398385987584), (7876478617/2475880078570760549798248448)), (15/9903520314283042199192993792), by norm_num⟩
  | 6 => ⟨((-53773760359/158456325028528675187087900672), (-34670397893/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((74382935595/2535301200456458802993406410752), (3946551663/316912650057057350374175801344)), (33/2535301200456458802993406410752), by norm_num⟩
  | 8 => ⟨((-92739613601/40564819207303340847894502572032), (-5432258011/10141204801825835211973625643008)), (43/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((3308027439/20282409603651670423947251286016), (6240978421/649037107316853453566312041152512)), (53/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((-55893719201/5192296858534827628530496329220096), (6307502653/5192296858534827628530496329220096)), (63/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((54974217875/83076749736557242056487941267521536), (-16024601565/83076749736557242056487941267521536)), (9/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((-50528554917/1329227995784915872903807060280344576), (12356938799/664613997892457936451903530140172288)), (19/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89049351891/4294967296), (25443338285/4294967296)), (11/4294967296), by norm_num⟩
  | 1 => ⟨((44176342085/34359738368), (1526353483/17179869184)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((41346558897/4398046511104), (-7421621457/4398046511104)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((-64176201691/562949953421312), (11896866733/281474976710656)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((72035367141/36028797018963968), (-42431191273/36028797018963968)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-46467684997/1152921504606846976), (39893602075/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 6 => ⟨((31501734311/36893488147419103232), (-4825507337/4611686018427387904)), (37/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-21104488451/1180591620717411303424), (1185568893/36893488147419103232)), (91/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((6451672725/18889465931478580854784), (-18771902027/18889465931478580854784)), (31/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-11587998285/2417851639229258349412352), (74364355781/2417851639229258349412352)), (161/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-199068219/9671406556917033397649408), (-4583069285/4835703278458516698824704)), (209/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((14363691219/2475880078570760549798248448), (71646492865/2475880078570760549798248448)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-27066550577/79228162514264337593543950336), (-68995466445/79228162514264337593543950336)), (167/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((495529969/2417851639229258349412352), (97965577929/154742504910672534362390528)), (3/19342813113834066795298816), by norm_num⟩
  | 1 => ⟨((-38855177119/309485009821345068724781056), (-36924800169/154742504910672534362390528)), (25/309485009821345068724781056), by norm_num⟩
  | 2 => ⟨((44974975265/1237940039285380274899124224), (58478911181/1237940039285380274899124224)), (23/1237940039285380274899124224), by norm_num⟩
  | 3 => ⟨((-4332456529/618970019642690137449562112), (-63796591641/9903520314283042199192993792)), (1/309485009821345068724781056), by norm_num⟩
  | 4 => ⟨((81665205293/79228162514264337593543950336), (6581660699/9903520314283042199192993792)), (37/79228162514264337593543950336), by norm_num⟩
  | 5 => ⟨((-79074782303/633825300114114700748351602688), (-33563903989/633825300114114700748351602688)), (37/633825300114114700748351602688), by norm_num⟩
  | 6 => ⟨((65726228717/5070602400912917605986812821504), (15399755017/5070602400912917605986812821504)), (33/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((-753575921/633825300114114700748351602688), (-2843417201/40564819207303340847894502572032)), (53/81129638414606681695789005144064), by norm_num⟩
  | 8 => ⟨((15915890097/162259276829213363391578010288128), (-1796078709/162259276829213363391578010288128)), (39/649037107316853453566312041152512), by norm_num⟩
  | 9 => ⟨((-76530957889/10384593717069655257060992658440192), (5577060279/2596148429267413814265248164610048)), (27/5192296858534827628530496329220096), by norm_num⟩
  | 10 => ⟨((84410449653/166153499473114484112975882535043072), (-41285754643/166153499473114484112975882535043072)), (71/166153499473114484112975882535043072), by norm_num⟩
  | 11 => ⟨((-42835323491/1329227995784915872903807060280344576), (15490212565/664613997892457936451903530140172288)), (11/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((39902731585/21267647932558653966460912964485513216), (-20436852687/10633823966279326983230456482242756608)), (13/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89049351891/4294967296), (25443338285/4294967296)), (3/1073741824), by norm_num⟩
  | 1 => ⟨((44176342085/34359738368), (1526353483/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((41346558897/4398046511104), (-7421621457/4398046511104)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-64176201691/562949953421312), (11896866733/281474976710656)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((72035367141/36028797018963968), (-42431191273/36028797018963968)), (23/36028797018963968), by norm_num⟩
  | 5 => ⟨((-46467684997/1152921504606846976), (39893602075/1152921504606846976)), (15/576460752303423488), by norm_num⟩
  | 6 => ⟨((31501734311/36893488147419103232), (-4825507337/4611686018427387904)), (19/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-42208976905/2361183241434822606848), (1185568893/36893488147419103232)), (23/590295810358705651712), by norm_num⟩
  | 8 => ⟨((25806690907/75557863725914323419136), (-75087608109/75557863725914323419136)), (125/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-11587998303/2417851639229258349412352), (37182177893/1208925819614629174706176)), (81/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-1592545713/77371252455336267181195264), (-73329108579/77371252455336267181195264)), (105/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((14363691139/2475880078570760549798248448), (71646492923/2475880078570760549798248448)), (257/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-6766637607/19807040628566084398385987584), (-68995466597/79228162514264337593543950336)), (335/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((61979502820849/65536), (-186179367780611/524288)), (4075705/1048576), by norm_num⟩
  | 1 => ⟨((39919308399/32), (-5960637637/16)), (353/64), by norm_num⟩
  | 2 => ⟨((105828211339/128), (-12096340175/64)), (63/16), by norm_num⟩
  | 3 => ⟨((94012359935/256), (-7702262563/128)), (121/64), by norm_num⟩
  | 4 => ⟨((62980541603/512), (-3251470209/256)), (11/16), by norm_num⟩
  | 5 => ⟨((8485483481/256), (-3117438689/2048)), (413/2048), by norm_num⟩
  | 6 => ⟨((122631963855/16384), (1081056805/16384)), (407/8192), by norm_num⟩
  | 7 => ⟨((23868173925/16384), (5872425873/65536)), (347/32768), by norm_num⟩
  | 8 => ⟨((32697875787/131072), (3681948173/131072)), (131/65536), by norm_num⟩
  | 9 => ⟨((40032725017/1048576), (101632257/16384)), (355/1048576), by norm_num⟩
  | 10 => ⟨((22173016459/4194304), (18753924923/16777216)), (875/16777216), by norm_num⟩
  | 11 => ⟨((44890244073/67108864), (23324784283/134217728)), (991/134217728), by norm_num⟩
  | 12 => ⟨((83731004307/1073741824), (12885006355/536870912)), (65/67108864), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((805491679420689/5070602400912917605986812821504), (-467893516543/10141204801825835211973625643008)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((907295462342325/316912650057057350374175801344), (-574570878667/633825300114114700748351602688)), (4473/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1930086723187871/39614081257132168796771975168), (-324075921165/19807040628566084398385987584)), (2523/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((966212598033431/1237940039285380274899124224), (-86269379323/309485009821345068724781056)), (5373/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1814138402379879/154742504910672534362390528), (-691825777709/154742504910672534362390528)), (2693/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1589866904116241/9671406556917033397649408), (-650367223587/9671406556917033397649408)), (633/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1294113095344385/604462909807314587353088), (-570858327369/604462909807314587353088)), (4445/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((243161055615851/9444732965739290427392), (-465504599327/37778931862957161709568)), (7249/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((670372232936309/2361183241434822606848), (-175303652367/1180591620717411303424)), (1365/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1680989905642571/590295810358705651712), (-969002470751/590295810358705651712)), (3773/295147905179352825856), by norm_num⟩
  | 8 => ⟨((237263133527043/9223372036854775808), (-1218547629187/73786976294838206464)), (4745/36893488147419103232), by norm_num⟩
  | 7 => ⟨((59590530071591/288230376151711744), (-1380971312165/9223372036854775808)), (10757/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1678498608925951/1152921504606846976), (-1393716654903/1152921504606846976)), (5429/576460752303423488), by norm_num⟩
  | 5 => ⟨((317232412909545/36028797018963968), (-1233998628543/144115188075855872)), (9615/144115188075855872), by norm_num⟩
  | 4 => ⟨((801984323691309/18014398509481984), (-1880390900159/36028797018963968)), (229/562949953421312), by norm_num⟩
  | 3 => ⟨((407775629946907/2251799813685248), (-1201419567715/4503599627370496)), (18735/9007199254740992), by norm_num⟩
  | 2 => ⟨((1257999387772641/2251799813685248), (-1241612007155/1125899906842624)), (4843/562949953421312), by norm_num⟩
  | 1 => ⟨((664831731083945/562949953421312), (-3932458360607/1125899906842624)), (30707/1125899906842624), by norm_num⟩
  | 0 => ⟨((1556635152559601/1125899906842624), (-136509700833/17592186044416)), (17085/281474976710656), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1556635152559601/1125899906842624), (-136509700833/17592186044416)), (65174103856944949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((134505555007287/70368744177664), (-24157975415397/1125899906842624)), (190031/1125899906842624), by norm_num⟩
  | 2 => ⟨((2056534027581465/562949953421312), (-11544123492159/140737488355328)), (367311/562949953421312), by norm_num⟩
  | 3 => ⟨((938626940173483/70368744177664), (-42172279500057/70368744177664)), (21437/4398046511104), by norm_num⟩
  | 4 => ⟨((97615474776847/549755813888), (-70315376041349/4398046511104)), (298789/2199023255552), by norm_num⟩
  | 5 => ⟨((1074514213624333/34359738368), (-97541442533907/17179869184)), (1807201/34359738368), by norm_num⟩
  | 6 => ⟨((61979502820849/65536), (-186179367780611/524288)), (4075705/1048576), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((89049351891/4294967296), (25443338285/4294967296)), (3/1073741824), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/11865121), (-3790080/11865121)), 0, by norm_num⟩
  | 1 => ⟨((4644799283200/140781096344641), (8538292224000/140781096344641)), 0, by norm_num⟩
  | 2 => ⟨((-56377624035/4398046511104), (-2147047571/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((45560426559/35184372088832), (-35202141897/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((13838825493/70368744177664), (55841728377/140737488355328)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((-92370513551/1125899906842624), (-7045771969/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 6 => ⟨((39577570655/4503599627370496), (-3521023099/281474976710656)), (1/562949953421312), by norm_num⟩
  | 7 => ⟨((2620263975/2251799813685248), (93354878517/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 8 => ⟨((-75560855873/144115188075855872), (-4333180331/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 9 => ⟨((34229688231/576460752303423488), (-11245486301/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 10 => ⟨((15738993177/2305843009213693952), (77898432869/4611686018427387904)), (21/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-61719539161/18446744073709551616), (-9470700391/18446744073709551616)), (11/4611686018427387904), by norm_num⟩
  | 12 => ⟨((58975037831/147573952589676412928), (-71667671031/147573952589676412928)), (91/147573952589676412928), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (2961/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (2961/1280)))⁻¹=value ((2252800/11865121), (-3790080/11865121)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/11865121), (-3790080/11865121))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/18009121), (-3790080/18009121)), 0, by norm_num⟩
  | 1 => ⟨((-388365516800/324328439192641), (14747959296000/324328439192641)), 0, by norm_num⟩
  | 2 => ⟨((-40950509335/8796093022208), (-22159838787/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((36350663145/35184372088832), (1915809545/35184372088832)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-4128707111/35184372088832), (57889387615/562949953421312)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((4180613985/2251799813685248), (-52820931021/2251799813685248)), (11/4503599627370496), by norm_num⟩
  | 6 => ⟨((40852176873/18014398509481984), (6146376279/2251799813685248)), (5/9007199254740992), by norm_num⟩
  | 7 => ⟨((-19175064297/36028797018963968), (-8107273307/144115188075855872)), (9/72057594037927936), by norm_num⟩
  | 8 => ⟨((73114785599/1152921504606846976), (-57560408167/1152921504606846976)), (1/36028797018963968), by norm_num⟩
  | 9 => ⟨((-14736022249/9223372036854775808), (27824231225/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-40477649003/36893488147419103232), (-27148981751/18446744073709551616)), (49/36893488147419103232), by norm_num⟩
  | 11 => ⟨((80692500941/295147905179352825856), (3213411007/73786976294838206464)), (85/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-80560733379/2361183241434822606848), (14204742937/590295810358705651712)), (73/1180591620717411303424), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (2961/1280)))⁻¹=value ((3891200/18009121), (-3790080/18009121)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/18009121), (-3790080/18009121))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5598611046400/213680399768641), (-23286251520000/213680399768641)), 0, by norm_num⟩
  | 1 => ⟨((75185717893/2199023255552), (33374851179/2199023255552)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-71804738735/8796093022208), (1250799451/274877906944)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((4604881707/17592186044416), (-72320093339/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((22096239715/70368744177664), (20684690737/70368744177664)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((-94460820543/1125899906842624), (4841173385/281474976710656)), (5/562949953421312), by norm_num⟩
  | 6 => ⟨((29364526437/4503599627370496), (-34314561071/2251799813685248)), (11/4503599627370496), by norm_num⟩
  | 7 => ⟨((7637410987/4503599627370496), (23845424211/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 8 => ⟨((-84700204073/144115188075855872), (-1471309641/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 9 => ⟨((17575344811/288230376151711744), (-25969001505/288230376151711744)), (25/576460752303423488), by norm_num⟩
  | 10 => ⟨((36537692479/4611686018427387904), (84685678307/4611686018427387904)), (13/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-33381410235/9223372036854775808), (-10274053143/18446744073709551616)), (53/18446744073709551616), by norm_num⟩
  | 12 => ⟨((32005041833/73786976294838206464), (-37609428383/73786976294838206464)), (27/36893488147419103232), by norm_num⟩
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
  | 0 => ⟨((27/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((204800/1015923), (-421120/3047769)), 0, by norm_num⟩
  | 1 => ⟨((-100072652800/9288895877361), (86245376000/3096298625787)), 0, by norm_num⟩
  | 2 => ⟨((-14750353461/17592186044416), (-15621311869/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((5803655819/17592186044416), (21116605097/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-30390346879/562949953421312), (-2098518633/281474976710656)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((26825242275/4503599627370496), (-26824403507/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((-444311989/1125899906842624), (12820592889/18014398509481984)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((-5413762005/576460752303423488), (-28534212161/288230376151711744)), (13/576460752303423488), by norm_num⟩
  | 8 => ⟨((2244171903/288230376151711744), (21512782923/2305843009213693952)), (19/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-52733699653/36893488147419103232), (-3712176647/9223372036854775808)), (53/73786976294838206464), by norm_num⟩
  | 10 => ⟨((101458272947/590295810358705651712), (-34344257115/590295810358705651712)), (73/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-31415051037/2361183241434822606848), (20942275965/1180591620717411303424)), (51/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((4365120449/37778931862957161709568), (-102273827179/37778931862957161709568)), (35/9444732965739290427392), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (2961/1280)))⁻¹=value ((204800/1015923), (-421120/3047769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((204800/1015923), (-421120/3047769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-44727114665/2199023255552), (-40348618755/2199023255552)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((54128050513/4398046511104), (-10734864141/8796093022208)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-38229406131/17592186044416), (13275659067/4398046511104)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-15533588093/70368744177664), (-3979850021/4398046511104)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((26554860577/140737488355328), (12923887627/140737488355328)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((-89844816967/2251799813685248), (42422108611/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 6 => ⟨((17374234263/9007199254740992), (-77716726477/9007199254740992)), (15/9007199254740992), by norm_num⟩
  | 7 => ⟨((19983998017/18014398509481984), (23460434663/18014398509481984)), (17/36028797018963968), by norm_num⟩
  | 8 => ⟨((-92717466321/288230376151711744), (883536289/36028797018963968)), (33/288230376151711744), by norm_num⟩
  | 9 => ⟨((8811931739/288230376151711744), (-3695379491/72057594037927936)), (17/576460752303423488), by norm_num⟩
  | 10 => ⟨((42390041361/9223372036854775808), (22801152309/2305843009213693952)), (69/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-72051531865/36893488147419103232), (-10750182833/36893488147419103232)), (35/18446744073709551616), by norm_num⟩
  | 12 => ⟨((34531090377/147573952589676412928), (-19792387409/73786976294838206464)), (71/147573952589676412928), by norm_num⟩
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
  | 0 => ⟨((35/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1024000/5732503), (-541440/5732503)), 0, by norm_num⟩
  | 1 => ⟨((-377709363200/32861590645009), (554434560000/32861590645009)), 0, by norm_num⟩
  | 2 => ⟨((4042790563/17592186044416), (-72118004217/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((10734555963/140737488355328), (13646167017/70368744177664)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-17981218079/1125899906842624), (-30890844115/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((9341656387/4503599627370496), (4242727109/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((-14952556987/72057594037927936), (8054199443/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 7 => ⟨((9162479623/576460752303423488), (-4263290423/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 8 => ⟨((-26603372109/36893488147419103232), (19108095369/9223372036854775808)), (9/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-4933864173/147573952589676412928), (-64663473129/295147905179352825856)), (21/295147905179352825856), by norm_num⟩
  | 10 => ⟨((15740399863/1180591620717411303424), (42475416863/2361183241434822606848)), (3/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-77082180159/37778931862957161709568), (-36912130933/37778931862957161709568)), (27/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((69022454349/302231454903657293676544), (-2747388741/302231454903657293676544)), (15/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (2961/1280)))⁻¹=value ((1024000/5732503), (-541440/5732503)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((1024000/5732503), (-541440/5732503))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-94404725553/17592186044416), (-11931916401/8796093022208)), (3/17592186044416), by norm_num⟩
  | 1 => ⟨((46206615421/17592186044416), (-26611819191/17592186044416)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((-4683548513/17592186044416), (35311044947/35184372088832)), (5/70368744177664), by norm_num⟩
  | 3 => ⟨((-41804355937/281474976710656), (-34199925529/140737488355328)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((9446171403/140737488355328), (14943449967/1125899906842624)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((-26952638973/2251799813685248), (41064088237/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 6 => ⟨((6054971927/36028797018963968), (-111801168431/36028797018963968)), (13/18014398509481984), by norm_num⟩
  | 7 => ⟨((65241120759/144115188075855872), (29755971747/72057594037927936)), (15/72057594037927936), by norm_num⟩
  | 8 => ⟨((-66339148797/576460752303423488), (693911467/36028797018963968)), (31/576460752303423488), by norm_num⟩
  | 9 => ⟨((46053430853/4611686018427387904), (-88559807863/4611686018427387904)), (63/4611686018427387904), by norm_num⟩
  | 10 => ⟨((2040564461/1152921504606846976), (64914843905/18446744073709551616)), (1/288230376151711744), by norm_num⟩
  | 11 => ⟨((-51698690375/73786976294838206464), (-7254043973/73786976294838206464)), (1/1152921504606846976), by norm_num⟩
  | 12 => ⟨((6174802227/73786976294838206464), (-13919734691/147573952589676412928)), (65/295147905179352825856), by norm_num⟩
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
  | 0 => ⟨((43/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/56101921), (-3790080/56101921)), 0, by norm_num⟩
  | 1 => ⟨((-31593987276800/3147425539890241), (33376960512000/3147425539890241)), 0, by norm_num⟩
  | 2 => ⟨((30233064233/70368744177664), (-82428133953/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((822873161/140737488355328), (59925281413/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-4565045311/1125899906842624), (-9184194919/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((10696310881/18014398509481984), (9066043525/18014398509481984)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-73327697929/1152921504606846976), (-22415963549/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((104197691793/18446744073709551616), (-11481089921/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-62321737875/147573952589676412928), (4420745753/18446744073709551616)), (9/73786976294838206464), by norm_num⟩
  | 9 => ⟨((7393513529/295147905179352825856), (-78093755895/2361183241434822606848)), (33/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-2004390527/2361183241434822606848), (65017446655/18889465931478580854784)), (31/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-7501319345/151115727451828646838272), (-45156674461/151115727451828646838272)), (57/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((33825155815/2417851639229258349412352), (26326167159/1208925819614629174706176)), (53/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (2961/1280)))⁻¹=value ((8806400/56101921), (-3790080/56101921)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/56101921), (-3790080/56101921))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-32862033745/35184372088832), (10527055217/70368744177664)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((26624027379/70368744177664), (-64483597287/140737488355328)), (5/140737488355328), by norm_num⟩
  | 2 => ⟨((3319041051/281474976710656), (31562240133/140737488355328)), (3/140737488355328), by norm_num⟩
  | 3 => ⟨((-27151462577/562949953421312), (-25509807087/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((37714281879/2251799813685248), (-2358037961/4503599627370496)), (13/4503599627370496), by norm_num⟩
  | 5 => ⟨((-23055671689/9007199254740992), (51282034403/18014398509481984)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-5657594017/72057594037927936), (-116494437027/144115188075855872)), (9/36028797018963968), by norm_num⟩
  | 7 => ⟨((76338140831/576460752303423488), (54780475941/576460752303423488)), (5/72057594037927936), by norm_num⟩
  | 8 => ⟨((-35010305449/1152921504606846976), (18014278755/2305843009213693952)), (43/2305843009213693952), by norm_num⟩
  | 9 => ⟨((2690547/1125899906842624), (-12285354191/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 10 => ⟨((18740936275/36893488147419103232), (68747707849/73786976294838206464)), (89/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-55477072979/295147905179352825856), (-7102794207/295147905179352825856)), (89/295147905179352825856), by norm_num⟩
  | 12 => ⟨((52723189153/2361183241434822606848), (-58840584769/2361183241434822606848)), (45/590295810358705651712), by norm_num⟩
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
  | 0 => ⟨((51/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/25117707), (-421120/8372569)), 0, by norm_num⟩
  | 1 => ⟨((-5262730035200/630899204937849), (1466171392000/210299734979283)), 0, by norm_num⟩
  | 2 => ⟨((3542977227/8796093022208), (-24381666401/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-2952195595/281474976710656), (4092389189/70368744177664)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-13252520593/18014398509481984), (-19339961129/4503599627370496)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((45823707989/288230376151711744), (5028192467/18014398509481984)), (9/288230376151711744), by norm_num⟩
  | 6 => ⟨((-41592729383/2305843009213693952), (-17693226421/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((30180314737/18446744073709551616), (2812951183/4611686018427387904)), (13/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-9498547285/73786976294838206464), (-666099611/590295810358705651712)), (21/590295810358705651712), by norm_num⟩
  | 9 => ⟨((42265428357/4722366482869645213696), (-7459405843/2361183241434822606848)), (33/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-40864712829/75557863725914323419136), (33550128229/75557863725914323419136)), (13/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((31814590141/1208925819614629174706176), (-26823303583/604462909807314587353088)), (5/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-13692555425/19342813113834066795298816), (72289817891/19342813113834066795298816)), (61/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (2961/1280)))⁻¹=value ((3481600/25117707), (-421120/8372569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/25117707), (-421120/8372569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-68644945303/562949953421312), (19059726009/281474976710656)), (7/562949953421312), by norm_num⟩
  | 1 => ⟨((5087123849/140737488355328), (-50833867925/562949953421312)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((28553101655/2251799813685248), (84801917379/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((-48595783245/4503599627370496), (-27680730959/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((3600188707/1125899906842624), (-6848837211/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 5 => ⟨((-14919862801/36028797018963968), (11825535851/18014398509481984)), (9/36028797018963968), by norm_num⟩
  | 6 => ⟨((-2835430357/72057594037927936), (-1477238085/9007199254740992)), (39/576460752303423488), by norm_num⟩
  | 7 => ⟨((69145601985/2305843009213693952), (38941984949/2305843009213693952)), (43/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-58284424877/9223372036854775808), (1264719729/576460752303423488)), (47/9223372036854775808), by norm_num⟩
  | 9 => ⟨((32911815051/73786976294838206464), (-86307087283/73786976294838206464)), (97/73786976294838206464), by norm_num⟩
  | 10 => ⟨((34171202795/295147905179352825856), (57812925999/295147905179352825856)), (49/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-94953528137/2361183241434822606848), (-2683131035/590295810358705651712)), (49/590295810358705651712), by norm_num⟩
  | 12 => ⟨((44796897553/9444732965739290427392), (-24903930507/4722366482869645213696)), (99/4722366482869645213696), by norm_num⟩
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
  | 0 => ⟨((59/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/97881121), (-3790080/97881121)), 0, by norm_num⟩
  | 1 => ⟨((-65819507916800/9580713848216641), (45796294656000/9580713848216641)), 0, by norm_num⟩
  | 2 => ⟨((5831776629/17592186044416), (-7530346729/17592186044416)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-27413437953/2251799813685248), (73946736633/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((4166524075/36028797018963968), (-40760151531/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((21137765803/576460752303423488), (81798620637/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-23107016433/4611686018427387904), (-74234970763/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((34317951055/73786976294838206464), (58997372295/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-10757397161/295147905179352825856), (-37003375885/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((48226501447/18889465931478580854784), (9885299523/37778931862957161709568)), (25/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-98317386503/604462909807314587353088), (20115711263/604462909807314587353088)), (17/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((45432601437/4835703278458516698824704), (-25160844759/4835703278458516698824704)), (23/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-2317145485/4835703278458516698824704), (38922048181/77371252455336267181195264)), (31/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (2961/1280)))⁻¹=value ((12083200/97881121), (-3790080/97881121)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/97881121), (-3790080/97881121))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55984224405/4503599627370496), (58910220035/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 1 => ⟨((3332007069/2251799813685248), (-122452011491/9007199254740992)), (15/9007199254740992), by norm_num⟩
  | 2 => ⟨((28781897583/9007199254740992), (22634105169/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 3 => ⟨((-67178768317/36028797018963968), (-21231035011/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 4 => ⟨((8859358841/18014398509481984), (-15665954909/72057594037927936)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-29888637097/576460752303423488), (34591307841/288230376151711744)), (31/576460752303423488), by norm_num⟩
  | 6 => ⟨((-11911258029/1152921504606846976), (-62566779851/2305843009213693952)), (35/2305843009213693952), by norm_num⟩
  | 7 => ⟨((25450996617/4611686018427387904), (11061076133/4611686018427387904)), (19/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-39926799989/36893488147419103232), (17499617073/36893488147419103232)), (83/73786976294838206464), by norm_num⟩
  | 9 => ⟨((9944468029/147573952589676412928), (-62540409531/295147905179352825856)), (87/295147905179352825856), by norm_num⟩
  | 10 => ⟨((51521165049/2361183241434822606848), (20118037323/590295810358705651712)), (11/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-16875448421/2361183241434822606848), (-6471018505/9444732965739290427392)), (177/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((15786410339/18889465931478580854784), (-70325754883/75557863725914323419136)), (89/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((67/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/123685921), (-3790080/123685921)), 0, by norm_num⟩
  | 1 => ⟨((-86958800076800/15298207053618241), (52005961728000/15298207053618241)), 0, by norm_num⟩
  | 2 => ⟨((9261152803/35184372088832), (-9698859759/35184372088832)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-46734311127/4503599627370496), (43512634641/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((20143718117/72057594037927936), (-22173141483/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((966122535/288230376151711744), (41826917903/576460752303423488)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-11968434723/9223372036854775808), (-9162059331/2305843009213693952)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((39212330427/295147905179352825856), (29591799907/147573952589676412928)), (9/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-12327457887/1180591620717411303424), (-10728396709/1180591620717411303424)), (11/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((27141511499/37778931862957161709568), (25998423331/75557863725914323419136)), (7/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-27275085987/604462909807314587353088), (-4883432635/604462909807314587353088)), (33/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((101616460031/38685626227668133590597632), (-294020923/1208925819614629174706176)), (19/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-21969853913/154742504910672534362390528), (33260795317/618970019642690137449562112)), (11/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (2961/1280)))⁻¹=value ((13721600/123685921), (-3790080/123685921)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/123685921), (-3790080/123685921))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-17622658503/18014398509481984), (4125478293/2251799813685248)), (13/36028797018963968), by norm_num⟩
  | 1 => ⟨((-16301940443/72057594037927936), (-60173896803/36028797018963968)), (5/18014398509481984), by norm_num⟩
  | 2 => ⟨((19694799507/36028797018963968), (19773155741/36028797018963968)), (13/72057594037927936), by norm_num⟩
  | 3 => ⟨((-37994963389/144115188075855872), (-545931569/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((36308692677/576460752303423488), (-47900884095/1152921504606846976)), (17/576460752303423488), by norm_num⟩
  | 5 => ⟨((-22743536527/4611686018427387904), (83805957045/4611686018427387904)), (11/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-18285170227/9223372036854775808), (-69677453137/18446744073709551616)), (13/4611686018427387904), by norm_num⟩
  | 7 => ⟨((15745901969/18446744073709551616), (20374128387/73786976294838206464)), (57/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-46368963377/295147905179352825856), (12329142291/147573952589676412928)), (31/147573952589676412928), by norm_num⟩
  | 9 => ⟨((9937254475/1180591620717411303424), (-77006775341/2361183241434822606848)), (65/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((33036083079/9444732965739290427392), (11924787949/2361183241434822606848)), (133/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-82001510871/75557863725914323419136), (-6313098227/75557863725914323419136)), (67/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((37982610319/302231454903657293676544), (-42572093535/302231454903657293676544)), (135/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((75/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/50922507), (-421120/16974169)), 0, by norm_num⟩
  | 1 => ⟨((-12309160755200/2593101719165049), (2156134400000/864367239721683)), 0, by norm_num⟩
  | 2 => ⟨((58460815249/281474976710656), (-25936060801/140737488355328)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-36728154099/4503599627370496), (26663441229/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((18958547939/72057594037927936), (-12545907017/18014398509481984)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((-2644628403/576460752303423488), (44128486735/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-9007936755/36893488147419103232), (-73089908967/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((21752189629/590295810358705651712), (57002702861/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-7202557627/2361183241434822606848), (-2595836379/590295810358705651712)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((62834296439/302231454903657293676544), (13844819019/75557863725914323419136)), (21/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-61532800809/4835703278458516698824704), (-8018440913/1208925819614629174706176)), (11/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((55860352703/77371252455336267181195264), (3396517405/19342813113834066795298816)), (23/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-95256614999/2475880078570760549798248448), (317677599/2475880078570760549798248448)), (47/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (2961/1280)))⁻¹=value ((5120000/50922507), (-421120/16974169)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/50922507), (-421120/16974169))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7624494605/144115188075855872), (60089218381/288230376151711744)), (7/144115188075855872), by norm_num⟩
  | 1 => ⟨((-18478152293/288230376151711744), (-24996833087/144115188075855872)), (11/288230376151711744), by norm_num⟩
  | 2 => ⟨((42630578617/576460752303423488), (28559748249/576460752303423488)), (15/576460752303423488), by norm_num⟩
  | 3 => ⟨((-36423281857/1152921504606846976), (4428357615/2305843009213693952)), (29/2305843009213693952), by norm_num⟩
  | 4 => ⟨((63332294487/9223372036854775808), (-28723690525/4611686018427387904)), (41/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-1443192285/4611686018427387904), (21654679885/9223372036854775808)), (55/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-45221217047/147573952589676412928), (-33389209103/73786976294838206464)), (33/73786976294838206464), by norm_num⟩
  | 7 => ⟨((16778057867/147573952589676412928), (7536021163/295147905179352825856)), (73/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-11661672989/590295810358705651712), (29336438387/2361183241434822606848)), (5/147573952589676412928), by norm_num⟩
  | 9 => ⟨((8275672377/9444732965739290427392), (-20578343247/4722366482869645213696)), (167/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((2299750091/4722366482869645213696), (49184049077/75557863725914323419136)), (43/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-86891212215/604462909807314587353088), (-1232991203/151115727451828646838272)), (87/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((39819806695/2417851639229258349412352), (-11275392823/604462909807314587353088)), (175/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((83/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/185125921), (-3790080/185125921)), 0, by norm_num⟩
  | 1 => ⟨((-137290448076800/34271606626098241), (64425295872000/34271606626098241)), 0, by norm_num⟩
  | 2 => ⟨((23175493247/140737488355328), (-35834937879/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-28178672071/4503599627370496), (67829339139/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((15144417447/72057594037927936), (-59055547659/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((-25153601779/4611686018427387904), (96682035461/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((660505403/18446744073709551616), (-37569543265/36893488147419103232)), (7/73786976294838206464), by norm_num⟩
  | 7 => ⟨((20731662653/2361183241434822606848), (111254671613/2361183241434822606848)), (13/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-16725247249/18889465931478580854784), (-19582095691/9444732965739290427392)), (13/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((37400520379/604462909807314587353088), (52058712249/604462909807314587353088)), (13/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-71999053205/19342813113834066795298816), (-32114955961/9671406556917033397649408)), (3/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((7925984663/38685626227668133590597632), (35388823297/309485009821345068724781056)), (11/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-52373386781/4951760157141521099596496896), (-3902559343/1237940039285380274899124224)), (5/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (2961/1280)))⁻¹=value ((16998400/185125921), (-3790080/185125921)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/185125921), (-3790080/185125921))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2719487209/4611686018427387904), (46637032909/2305843009213693952)), (13/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-5544137787/576460752303423488), (-4481533083/288230376151711744)), (11/2305843009213693952), by norm_num⟩
  | 2 => ⟨((77525736701/9223372036854775808), (16834779191/4611686018427387904)), (15/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-60593099735/18446744073709551616), (3419908049/4611686018427387904)), (15/9223372036854775808), by norm_num⟩
  | 4 => ⟨((47680074631/73786976294838206464), (-28782445081/36893488147419103232)), (11/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-693200031/295147905179352825856), (39020872447/147573952589676412928)), (59/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-47223389075/1180591620717411303424), (-56006733005/1180591620717411303424)), (73/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((62732341645/4722366482869645213696), (8431060715/4722366482869645213696)), (41/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-41325715283/18889465931478580854784), (1888116795/1180591620717411303424)), (89/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((5690369415/75557863725914323419136), (-38827629327/75557863725914323419136)), (47/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((36174337999/604462909807314587353088), (44829059479/604462909807314587353088)), (97/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-81592460185/4835703278458516698824704), (-1447019187/2417851639229258349412352)), (197/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((36965624791/19342813113834066795298816), (-42461337861/19342813113834066795298816)), (397/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((91/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2662400/31537303), (-541440/31537303)), 0, by norm_num⟩
  | 1 => ⟨((-3397608243200/994601480513809), (1441529856000/994601480513809)), 0, by norm_num⟩
  | 2 => ⟨((37084655925/281474976710656), (-50947817547/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-21546952133/4503599627370496), (44595240537/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((5744788239/36028797018963968), (-72073699863/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-2642452007/576460752303423488), (27494130829/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((13449099003/147573952589676412928), (-10010150935/18446744073709551616)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((3831545287/4722366482869645213696), (3495702961/147573952589676412928)), (7/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-4487887587/18889465931478580854784), (-75021799841/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((11213896249/604462909807314587353088), (3012596741/75557863725914323419136)), (11/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-21767238833/19342813113834066795298816), (-58946573607/38685626227668133590597632)), (19/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((585902297/9671406556917033397649408), (16915593573/309485009821345068724781056)), (1/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-59942505345/19807040628566084398385987584), (-35396494123/19807040628566084398385987584)), (27/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (2961/1280)))⁻¹=value ((2662400/31537303), (-541440/31537303)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((2662400/31537303), (-541440/31537303))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10974165407/36893488147419103232), (7920947203/4611686018427387904)), (11/18446744073709551616), by norm_num⟩
  | 1 => ⟨((-40810048941/36893488147419103232), (-5614449477/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 2 => ⟨((30599450929/36893488147419103232), (15182575005/73786976294838206464)), (27/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-88941489965/295147905179352825856), (34659837029/295147905179352825856)), (55/295147905179352825856), by norm_num⟩
  | 4 => ⟨((15604307909/295147905179352825856), (-12469742069/147573952589676412928)), (21/295147905179352825856), by norm_num⟩
  | 5 => ⟨((1673479121/590295810358705651712), (62295119491/2361183241434822606848)), (57/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-21427269767/4722366482869645213696), (-10406802203/2361183241434822606848)), (71/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((52190167411/37778931862957161709568), (5269866837/75557863725914323419136)), (161/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-65326165939/302231454903657293676544), (857054891/4722366482869645213696)), (11/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1541717823/302231454903657293676544), (-65513037627/1208925819614629174706176)), (187/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((63592491061/9671406556917033397649408), (73161299777/9671406556917033397649408)), (387/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-68751342427/38685626227668133590597632), (-114656211/4835703278458516698824704)), (197/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((61545942649/309485009821345068724781056), (-17979900707/77371252455336267181195264)), (795/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((99/8), (2961/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/28852569), (-421120/28852569)), 0, by norm_num⟩
  | 1 => ⟨((-90699366400/30832249551843), (948699136000/832470737899761)), 0, by norm_num⟩
  | 2 => ⟨((59969373739/562949953421312), (-37131324965/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-66247001625/18014398509481984), (60391850195/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((17164368179/144115188075855872), (-45458329189/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-32270188865/9223372036854775808), (32403365247/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 6 => ⟨((25180078005/295147905179352825856), (-44248738999/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-42148807/36893488147419103232), (58218996827/4722366482869645213696)), (13/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-3427971047/75557863725914323419136), (-36995726341/75557863725914323419136)), (11/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((25844130221/4835703278458516698824704), (90834626347/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-26749488937/77371252455336267181195264), (-26860522003/38685626227668133590597632)), (7/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((22981455753/1237940039285380274899124224), (60865580825/2475880078570760549798248448)), (11/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-35817111589/39614081257132168796771975168), (-65304176797/79228162514264337593543950336)), (33/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (2961/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (2961/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (2961/1280)))⁻¹=value ((2252800/28852569), (-421120/28852569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/28852569), (-421120/28852569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((28507938613/590295810358705651712), (38300378267/295147905179352825856)), (17/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-63144052815/590295810358705651712), (-24682018501/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 2 => ⟨((42825307149/590295810358705651712), (3804091999/590295810358705651712)), (11/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-7288472157/295147905179352825856), (32691135361/2361183241434822606848)), (45/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((17745483199/4722366482869645213696), (-76407785879/9444732965739290427392)), (71/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((9799231531/18889465931478580854784), (44614170767/18889465931478580854784)), (49/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-8615431363/18889465931478580854784), (-55357793729/151115727451828646838272)), (123/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((19548555325/151115727451828646838272), (-2263491219/604462909807314587353088)), (71/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-46545152369/2417851639229258349412352), (22263075349/1208925819614629174706176)), (39/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((2171146399/9671406556917033397649408), (-99907729239/19342813113834066795298816)), (333/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((50503248249/77371252455336267181195264), (54002233491/77371252455336267181195264)), (173/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-105029444533/618970019642690137449562112), (124017331/77371252455336267181195264)), (353/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((23209308989/1237940039285380274899124224), (-864545983/38685626227668133590597632)), (357/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((50442749207/549755813888), (58040371545/549755813888)), (211/274877906944), by norm_num⟩
  | 1 => ⟨((-12244192507/549755813888), (14127070727/137438953472)), (519/274877906944), by norm_num⟩
  | 2 => ⟨((-64302044089/2199023255552), (30834795415/2199023255552)), (2479/1099511627776), by norm_num⟩
  | 3 => ⟨((-37265128361/8796093022208), (-22847027253/17592186044416)), (16163/8796093022208), by norm_num⟩
  | 4 => ⟨((-69394714717/140737488355328), (24952686757/140737488355328)), (81763/70368744177664), by norm_num⟩
  | 5 => ⟨((-26539865461/140737488355328), (-7720739961/281474976710656)), (340461/562949953421312), by norm_num⟩
  | 6 => ⟨((-13878075969/2251799813685248), (-26113569953/1125899906842624)), (1209689/4503599627370496), by norm_num⟩
  | 7 => ⟨((30153087385/72057594037927936), (99418812957/72057594037927936)), (7524641/72057594037927936), by norm_num⟩
  | 8 => ⟨((-25118450563/36028797018963968), (-2828153561/18014398509481984)), (5223207/144115188075855872), by norm_num⟩
  | 9 => ⟨((924779747/18014398509481984), (-61515864563/576460752303423488)), (6580357/576460752303423488), by norm_num⟩
  | 10 => ⟨((2130971723/288230376151711744), (38549573495/2305843009213693952)), (1907579/576460752303423488), by norm_num⟩
  | 11 => ⟨((-67530955405/18446744073709551616), (-6389291609/9223372036854775808)), (16490817/18446744073709551616), by norm_num⟩
  | 12 => ⟨((15947944863/36893488147419103232), (-19298303587/36893488147419103232)), (16790143/73786976294838206464), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((50442749207/549755813888), (58040371545/549755813888)), (423/549755813888), by norm_num⟩
  | 1 => ⟨((-12244192507/549755813888), (14127070727/137438953472)), (1039/549755813888), by norm_num⟩
  | 2 => ⟨((-64302044089/2199023255552), (30834795415/2199023255552)), (4959/2199023255552), by norm_num⟩
  | 3 => ⟨((-37265128361/8796093022208), (-22847027253/17592186044416)), (32327/17592186044416), by norm_num⟩
  | 4 => ⟨((-69394714717/140737488355328), (24952686757/140737488355328)), (40883/35184372088832), by norm_num⟩
  | 5 => ⟨((-26539865461/140737488355328), (-7720739961/281474976710656)), (85121/140737488355328), by norm_num⟩
  | 6 => ⟨((-13878075969/2251799813685248), (-26113569953/1125899906842624)), (604935/2251799813685248), by norm_num⟩
  | 7 => ⟨((30153087385/72057594037927936), (99418812957/72057594037927936)), (1881881/18014398509481984), by norm_num⟩
  | 8 => ⟨((-25118450563/36028797018963968), (-2828153561/18014398509481984)), (1307243/36028797018963968), by norm_num⟩
  | 9 => ⟨((924779747/18014398509481984), (-61515864563/576460752303423488)), (825427/72057594037927936), by norm_num⟩
  | 10 => ⟨((2130971723/288230376151711744), (38549573495/2305843009213693952)), (3861275/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-67530955405/18446744073709551616), (-6389291609/9223372036854775808)), (17228687/18446744073709551616), by norm_num⟩
  | 12 => ⟨((15947944863/36893488147419103232), (-19298303587/36893488147419103232)), (19741623/73786976294838206464), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile010Gamma
