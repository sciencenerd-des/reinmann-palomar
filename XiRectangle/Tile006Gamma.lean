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
namespace Reinmann.XiRectangle.Tile006Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1833/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1833/640))
  have he : value ((3/4), (1833/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/296454289), (-2346240/296454289)), 0, by norm_num⟩
  | 1 => ⟨((-237350511411200/87885145466495521), (51414564864000/87885145466495521)), 0, by norm_num⟩
  | 2 => ⟨((54888238823/562949953421312), (-18188422783/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-62613336261/18014398509481984), (7115495677/4503599627370496)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((70448902869/576460752303423488), (-2599424083/36028797018963968)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((-78053564001/18446744073709551616), (29055241423/9223372036854775808)), (5/18446744073709551616), by norm_num⟩
  | 6 => ⟨((42477872623/295147905179352825856), (-39305682527/295147905179352825856)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-5657685357/1180591620717411303424), (25932963675/4722366482869645213696)), (3/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((11740793095/75557863725914323419136), (-8384182879/37778931862957161709568)), (9/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-23525022635/4835703278458516698824704), (85274956535/9671406556917033397649408)), (13/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((22423972635/154742504910672534362390528), (-13351616483/38685626227668133590597632)), (9/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-19758085813/4951760157141521099596496896), (66003562709/4951760157141521099596496896)), (13/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((3752492045/39614081257132168796771975168), (-40282308293/79228162514264337593543950336)), (9/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (1833/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (1833/1280)))⁻¹=value ((21913600/296454289), (-2346240/296454289)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/296454289), (-2346240/296454289))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89303930109/34359738368), (458107329/4294967296)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((10956800/296454289), (-1173120/296454289)), 0, by norm_num⟩
  | 2 => ⟨((-59337627852800/87885145466495521), (12853641216000/87885145466495521)), 0, by norm_num⟩
  | 3 => ⟨((73184318431/4503599627370496), (-24251230377/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-62613336261/144115188075855872), (7115495677/36028797018963968)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((56359122295/4611686018427387904), (-16636314131/2305843009213693952)), (3/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-26017854667/73786976294838206464), (38740321897/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((48546140141/4722366482869645213696), (-44920780031/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-5657685357/18889465931478580854784), (25932963675/75557863725914323419136)), (3/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((10436260529/1208925819614629174706176), (-14905214007/1208925819614629174706176)), (9/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-4705004527/19342813113834066795298816), (17054991307/38685626227668133590597632)), (11/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((32616687469/4951760157141521099596496896), (-77682132265/4951760157141521099596496896)), (7/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-26344114417/158456325028528675187087900672), (88004750279/158456325028528675187087900672)), (9/79228162514264337593543950336), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (39/20480)), 0, by norm_num⟩
  | 45 => ⟨((106876209857/4080638361600), (-77493/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-51315654786151/1915179604377600), (1639352148941/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((120524864451/4398046511104), (-12542824153/4398046511104)), (1/4398046511104), by norm_num⟩
  | 42 => ⟨((-30841599109/1099511627776), (50175851/17179869184)), (1/4398046511104), by norm_num⟩
  | 41 => ⟨((63179786165/2199023255552), (-6574459587/2199023255552)), (1/2199023255552), by norm_num⟩
  | 40 => ⟨((-64752588083/2199023255552), (841667067/274877906944)), (1/2199023255552), by norm_num⟩
  | 39 => ⟨((8300754549/274877906944), (-6900171129/2199023255552)), (1/2199023255552), by norm_num⟩
  | 38 => ⟨((-68146194593/2199023255552), (3537764641/1099511627776)), (1/2199023255552), by norm_num⟩
  | 37 => ⟨((69980022321/2199023255552), (-7260046537/2199023255552)), (1/2199023255552), by norm_num⟩
  | 36 => ⟨((-17978822097/549755813888), (3727225031/1099511627776)), (1/2199023255552), by norm_num⟩
  | 35 => ⟨((36980325017/1099511627776), (-1914888621/549755813888)), (1/2199023255552), by norm_num⟩
  | 34 => ⟨((-76125778635/2199023255552), (3938134145/1099511627776)), (1/2199023255552), by norm_num⟩
  | 33 => ⟨((1225336133/34359738368), (-8105606137/2199023255552)), (1/2199023255552), by norm_num⟩
  | 32 => ⟨((-10107504819/274877906944), (260897017/68719476736)), (1/2199023255552), by norm_num⟩
  | 31 => ⟨((41727554381/1099511627776), (-8606840719/2199023255552)), (1/2199023255552), by norm_num⟩
  | 30 => ⟨((-10777787489/274877906944), (4440727519/1099511627776)), (1/2199023255552), by norm_num⟩
  | 29 => ⟨((89179326629/2199023255552), (-4587088981/1099511627776)), (1/2199023255552), by norm_num⟩
  | 28 => ⟨((-46173210635/1099511627776), (2371715621/549755813888)), (1/2199023255552), by norm_num⟩
  | 27 => ⟨((95746797779/2199023255552), (-2455405861/549755813888)), (1/2199023255552), by norm_num⟩
  | 26 => ⟨((-99407222051/2199023255552), (10180885503/2199023255552)), (1/2199023255552), by norm_num⟩
  | 25 => ⟨((103358718453/2199023255552), (-1320930257/274877906944)), (1/2199023255552), by norm_num⟩
  | 24 => ⟨((-13454681503/274877906944), (1373066017/274877906944)), (1/2199023255552), by norm_num⟩
  | 23 => ⟨((112285839513/2199023255552), (-11435911333/2199023255552)), (1/2199023255552), by norm_num⟩
  | 22 => ⟨((-58676980835/1099511627776), (2981501537/549755813888)), (1/2199023255552), by norm_num⟩
  | 21 => ⟨((122901376615/2199023255552), (-1557502395/274877906944)), (1/2199023255552), by norm_num⟩
  | 20 => ⟨((-32249868457/549755813888), (6522067571/1099511627776)), (1/1099511627776), by norm_num⟩
  | 19 => ⟨((33933641671/549755813888), (-6842879141/1099511627776)), (1/1099511627776), by norm_num⟩
  | 18 => ⟨((-35803002223/549755813888), (7196914271/1099511627776)), (1/1099511627776), by norm_num⟩
  | 17 => ⟨((18945219199/274877906944), (-7589621001/1099511627776)), (1/1099511627776), by norm_num⟩
  | 16 => ⟨((-20118247733/274877906944), (4013854339/549755813888)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((42892439827/549755813888), (-8519535817/1099511627776)), (1/1099511627776), by norm_num⟩
  | 14 => ⟨((-22962027891/274877906944), (9075650623/1099511627776)), (1/1099511627776), by norm_num⟩
  | 13 => ⟨((24708589967/274877906944), (-4854779653/549755813888)), (1/1099511627776), by norm_num⟩
  | 12 => ⟨((-106971956625/1099511627776), (5219421409/549755813888)), (1/1099511627776), by norm_num⟩
  | 11 => ⟨((58285696169/549755813888), (-11286821697/1099511627776)), (1/1099511627776), by norm_num⟩
  | 10 => ⟨((-64032982123/549755813888), (6142555739/549755813888)), (1/549755813888), by norm_num⟩
  | 9 => ⟨((71039619715/549755813888), (-6738840015/549755813888)), (1/549755813888), by norm_num⟩
  | 8 => ⟨((-39885637501/274877906944), (3731887827/274877906944)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((90955997147/549755813888), (-8364210609/549755813888)), (1/549755813888), by norm_num⟩
  | 6 => ⟨((-105799824077/549755813888), (1189124087/68719476736)), (1/549755813888), by norm_num⟩
  | 5 => ⟨((31614378747/137438953472), (-2757504065/137438953472)), (1/274877906944), by norm_num⟩
  | 4 => ⟨((-78599340763/274877906944), (6563903311/274877906944)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((103933691159/274877906944), (-2027921225/68719476736)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((-38441140759/68719476736), (5316545829/137438953472)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((37394152887/34359738368), (-1938340039/34359738368)), (1/68719476736), by norm_num⟩
  | 0 => ⟨((-23845971955/137438953472), (7329717263/68719476736)), (1/137438953472), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (1833/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (1833/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (1833/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((89303930109/34359738368), (458107329/4294967296)), (1/17179869184), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (1833/1280))) (z:=((-21/128), (1833/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((89303930109/34359738368), (458107329/4294967296))) (r:=(1/17179869184)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((35766872127/1073741824), (10941942097/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((122393749993/68719476736), (950206489/17179869184)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((841716402355200/87885145466495521), (-93370934485920/87885145466495521)), 0, by norm_num⟩
  | 3 => ⟨((-67922068575/562949953421312), (15238075355/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((81010985465/36028797018963968), (-27808978215/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-57135559297/1152921504606846976), (26928664701/1152921504606846976)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((44077211863/36893488147419103232), (-27024292413/36893488147419103232)), (7/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-71605917125/2361183241434822606848), (55504848601/2361183241434822606848)), (19/590295810358705651712), by norm_num⟩
  | 8 => ⟨((59861510855/75557863725914323419136), (-14471815467/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-25334344867/1208925819614629174706176), (61008260541/2417851639229258349412352)), (113/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((42806042747/77371252455336267181195264), (-64751676125/77371252455336267181195264)), (19/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-35528743661/2475880078570760549798248448), (4314690827/154742504910672534362390528)), (189/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((28330486919/79228162514264337593543950336), (-18447318937/19807040628566084398385987584)), (121/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21405575231/1073741824), (1966669601/536870912)), (5/4294967296), by norm_num⟩
  | 1 => ⟨((88034011625/68719476736), (950206489/17179869184)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((841716402355200/87885145466495521), (-93370934485920/87885145466495521)), 0, by norm_num⟩
  | 3 => ⟨((-67922068575/562949953421312), (15238075355/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((81010985465/36028797018963968), (-27808978215/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-57135559297/1152921504606846976), (26928664701/1152921504606846976)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((44077211863/36893488147419103232), (-27024292413/36893488147419103232)), (7/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-71605917125/2361183241434822606848), (55504848601/2361183241434822606848)), (19/590295810358705651712), by norm_num⟩
  | 8 => ⟨((59861510855/75557863725914323419136), (-14471815467/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-25334344867/1208925819614629174706176), (61008260541/2417851639229258349412352)), (113/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((42806042747/77371252455336267181195264), (-64751676125/77371252455336267181195264)), (19/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-35528743661/2475880078570760549798248448), (4314690827/154742504910672534362390528)), (189/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((28330486919/79228162514264337593543950336), (-18447318937/19807040628566084398385987584)), (121/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((89569111871/4294967296), (1966669601/536870912)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((88034011625/68719476736), (950206489/17179869184)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((841716402355200/87885145466495521), (-93370934485920/87885145466495521)), 0, by norm_num⟩
  | 3 => ⟨((-67922068575/562949953421312), (15238075355/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((81010985465/36028797018963968), (-27808978215/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-57135559297/1152921504606846976), (26928664701/1152921504606846976)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((44077211863/36893488147419103232), (-27024292413/36893488147419103232)), (7/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-71605917125/2361183241434822606848), (55504848601/2361183241434822606848)), (19/590295810358705651712), by norm_num⟩
  | 8 => ⟨((59861510855/75557863725914323419136), (-14471815467/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-25334344867/1208925819614629174706176), (61008260541/2417851639229258349412352)), (113/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((42806042747/77371252455336267181195264), (-64751676125/77371252455336267181195264)), (19/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-35528743661/2475880078570760549798248448), (4314690827/154742504910672534362390528)), (189/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((28330486919/79228162514264337593543950336), (-18447318937/19807040628566084398385987584)), (121/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((474701022822400/87885145466495521), (-102829129728000/87885145466495521)), 0, by norm_num⟩
  | 1 => ⟨((-54888238823/140737488355328), (18188422783/140737488355328)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((11740000549/562949953421312), (-21346487031/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-70448902869/72057594037927936), (2599424083/4503599627370496)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((48783477501/1152921504606846976), (-36319051779/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-31858404467/18446744073709551616), (58958523791/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 6 => ⟨((19801898749/295147905179352825856), (-45382686431/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-11740793095/4722366482869645213696), (67073463031/18889465931478580854784)), (1/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((827051577/9444732965739290427392), (-23983581525/151115727451828646838272)), (7/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-28029965793/9671406556917033397649408), (33379041207/4835703278458516698824704)), (11/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((27167367993/309485009821345068724781056), (-22688724681/77371252455336267181195264)), (1/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-11257476135/4951760157141521099596496896), (60423462439/4951760157141521099596496896)), (3/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((3067388013/79228162514264337593543950336), (-78962632269/158456325028528675187087900672)), (9/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((54888238823/140737488355328), (-18188422783/140737488355328)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-11740000549/281474976710656), (21346487031/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((1651146161/562949953421312), (-7798272249/4503599627370496)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((-48783477501/288230376151711744), (36319051779/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((2488937849/288230376151711744), (-36849077369/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-59405696247/147573952589676412928), (68074029647/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 6 => ⟨((5136596979/295147905179352825856), (-7336160019/295147905179352825856)), (7/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-827051577/1180591620717411303424), (23983581525/18889465931478580854784)), (7/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((31533711517/1208925819614629174706176), (-18775710679/302231454903657293676544)), (11/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-16979604995/19342813113834066795298816), (28360905851/9671406556917033397649408)), (5/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((7739514843/309485009821345068724781056), (-83082260853/618970019642690137449562112)), (1/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-9202164039/19807040628566084398385987584), (59221974201/9903520314283042199192993792)), (25/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-2400449729/316912650057057350374175801344), (-82395464129/316912650057057350374175801344)), (5/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62613336261/2251799813685248), (-7115495677/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-70448902869/18014398509481984), (2599424083/1125899906842624)), (3/18014398509481984), by norm_num⟩
  | 2 => ⟨((48783477501/144115188075855872), (-36319051779/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-53097340779/2305843009213693952), (49132103159/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 4 => ⟨((49504746873/36893488147419103232), (-56728358039/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-5136596979/73786976294838206464), (7336160019/73786976294838206464)), (7/590295810358705651712), by norm_num⟩
  | 6 => ⟨((1929787013/590295810358705651712), (-55961690225/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-21022474345/151115727451828646838272), (25034280905/75557863725914323419136)), (1/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((25469407493/4835703278458516698824704), (-85082717553/4835703278458516698824704)), (15/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-3224797851/19342813113834066795298816), (34617608689/38685626227668133590597632)), (7/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((2108829259/618970019642690137449562112), (-13571702421/309485009821345068724781056)), (23/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((2400449729/39614081257132168796771975168), (82395464129/39614081257132168796771975168)), (19/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-8295445135/633825300114114700748351602688), (-30357955313/316912650057057350374175801344)), (1/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((70448902869/36028797018963968), (-2599424083/2251799813685248)), (3/36028797018963968), by norm_num⟩
  | 1 => ⟨((-48783477501/144115188075855872), (36319051779/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 2 => ⟨((2488937849/72057594037927936), (-36849077369/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 3 => ⟨((-49504746873/18446744073709551616), (56728358039/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 4 => ⟨((25682984895/147573952589676412928), (-73361600191/295147905179352825856)), (9/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-5789361039/590295810358705651712), (41971267669/2361183241434822606848)), (11/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((4598666263/9444732965739290427392), (-1369062237/1180591620717411303424)), (13/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-25469407493/1208925819614629174706176), (85082717553/1208925819614629174706176)), (7/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((7255795165/9671406556917033397649408), (-38944809775/9671406556917033397649408)), (15/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-5272073147/309485009821345068724781056), (67858512105/309485009821345068724781056)), (15/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-3300618377/9903520314283042199192993792), (-113293763177/9903520314283042199192993792)), (27/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((6221583851/79228162514264337593543950336), (91073865939/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-17499475727/2535301200456458802993406410752), (-70758487769/2535301200456458802993406410752)), (21/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((78053564001/576460752303423488), (-29055241423/288230376151711744)), (5/576460752303423488), by norm_num⟩
  | 1 => ⟨((-31858404467/1152921504606846976), (58958523791/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 2 => ⟨((7425712031/2305843009213693952), (-34037014823/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-5136596979/18446744073709551616), (7336160019/18446744073709551616)), (7/147573952589676412928), by norm_num⟩
  | 4 => ⟨((5789361039/295147905179352825856), (-41971267669/1180591620717411303424)), (11/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-11036799031/9444732965739290427392), (52571989901/18889465931478580854784)), (1/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((17828585245/302231454903657293676544), (-3722368893/18889465931478580854784)), (5/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-1451159033/604462909807314587353088), (7788961955/604462909807314587353088)), (3/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((9489731665/154742504910672534362390528), (-61072660895/77371252455336267181195264)), (25/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((1650309189/1237940039285380274899124224), (113293763177/2475880078570760549798248448)), (27/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-13687484473/39614081257132168796771975168), (-100181252533/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((2624921359/79228162514264337593543950336), (84910185323/633825300114114700748351602688)), (25/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-1575517667/633825300114114700748351602688), (-34624911593/5070602400912917605986812821504)), (3/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((42477872623/4611686018427387904), (-39305682527/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 1 => ⟨((-19801898749/9223372036854775808), (45382686431/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 2 => ⟨((5136596979/18446744073709551616), (-7336160019/18446744073709551616)), (1/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-1929787013/73786976294838206464), (55961690225/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((4598666263/2361183241434822606848), (-1369062237/295147905179352825856)), (13/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-17828585245/151115727451828646838272), (59557902287/151115727451828646838272)), (5/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((13544150975/2417851639229258349412352), (-72696978247/2417851639229258349412352)), (13/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-6326487777/38685626227668133590597632), (81430214527/38685626227668133590597632)), (9/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((-2475463783/618970019642690137449562112), (-84970322383/618970019642690137449562112)), (5/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((11406237061/9903520314283042199192993792), (83484377111/9903520314283042199192993792)), (11/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-4812355825/39614081257132168796771975168), (-38917168273/79228162514264337593543950336)), (3/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((25208282673/2535301200456458802993406410752), (34624911593/1267650600228229401496703205376)), (3/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-14468623761/20282409603651670423947251286016), (-29516218149/20282409603651670423947251286016)), (3/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5657685357/9223372036854775808), (-25932963675/36893488147419103232)), (3/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-46963172379/295147905179352825856), (67073463031/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 2 => ⟨((827051577/36893488147419103232), (-23983581525/590295810358705651712)), (7/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-21022474345/9444732965739290427392), (25034280905/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((25469407493/151115727451828646838272), (-85082717553/151115727451828646838272)), (7/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-1451159033/151115727451828646838272), (7788961955/151115727451828646838272)), (3/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((6326487777/19342813113834066795298816), (-81430214527/19342813113834066795298816)), (17/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((1414550733/154742504910672534362390528), (97108939867/309485009821345068724781056)), (23/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-14665161935/4951760157141521099596496896), (-53668528143/2475880078570760549798248448)), (29/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((13749588071/39614081257132168796771975168), (13898988669/9903520314283042199192993792)), (17/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-9903253907/316912650057057350374175801344), (-54410575361/633825300114114700748351602688)), (5/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((6200838755/2535301200456458802993406410752), (50599231113/10141204801825835211973625643008)), (21/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-28296045489/162259276829213363391578010288128), (-44889926931/162259276829213363391578010288128)), (21/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11740793095/295147905179352825856), (-8384182879/147573952589676412928)), (9/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-827051577/73786976294838206464), (23983581525/1180591620717411303424)), (7/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((31533711517/18889465931478580854784), (-18775710679/4722366482869645213696)), (3/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-25469407493/151115727451828646838272), (85082717553/151115727451828646838272)), (15/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((7255795165/604462909807314587353088), (-38944809775/604462909807314587353088)), (15/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-9489731665/19342813113834066795298816), (61072660895/9671406556917033397649408)), (13/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((-2475463783/154742504910672534362390528), (-84970322383/154742504910672534362390528)), (5/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((14665161935/2475880078570760549798248448), (53668528143/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-3867071645/4951760157141521099596496896), (-62545449011/19807040628566084398385987584)), (19/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((1547383423/19807040628566084398385987584), (68013219201/316912650057057350374175801344)), (3/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-34104613151/5070602400912917605986812821504), (-69573942781/5070602400912917605986812821504)), (29/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((21222034117/40564819207303340847894502572032), (67334890397/81129638414606681695789005144064)), (33/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-48937781743/1298074214633706907132624082305024), (-61885465859/1298074214633706907132624082305024)), (35/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((23525022635/9444732965739290427392), (-85274956535/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((-28029965793/37778931862957161709568), (33379041207/18889465931478580854784)), (11/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((16979604995/151115727451828646838272), (-56721811703/151115727451828646838272)), (5/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-12899191405/1208925819614629174706176), (34617608689/604462909807314587353088)), (7/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((5272073147/9671406556917033397649408), (-67858512105/9671406556917033397649408)), (15/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((1650309189/77371252455336267181195264), (56646881589/77371252455336267181195264)), (27/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((-11406237061/1237940039285380274899124224), (-83484377111/1237940039285380274899124224)), (23/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((13749588071/9903520314283042199192993792), (13898988669/2475880078570760549798248448)), (17/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-1547383423/9903520314283042199192993792), (-68013219201/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((37894014613/2535301200456458802993406410752), (19326095217/633825300114114700748351602688)), (1/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-51876083397/40564819207303340847894502572032), (-82298199375/40564819207303340847894502572032)), (5/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((32625187829/324518553658426726783156020576256), (41256977239/324518553658426726783156020576256)), (3/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((-19166997459/2596148429267413814265248164610048), (-39080538519/5192296858534827628530496329220096)), (27/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22423972635/151115727451828646838272), (-13351616483/37778931862957161709568)), (9/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((-3395920999/75557863725914323419136), (22688724681/151115727451828646838272)), (1/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((15479029685/2417851639229258349412352), (-41541130427/1208925819614629174706176)), (17/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((-2108829259/4835703278458516698824704), (108573619369/19342813113834066795298816)), (3/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((-1650309189/77371252455336267181195264), (-113293763177/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((13687484473/1237940039285380274899124224), (100181252533/1237940039285380274899124224)), (27/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-4812355825/2475880078570760549798248448), (-77834336547/9903520314283042199192993792)), (25/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((9903253907/39614081257132168796771975168), (54410575361/79228162514264337593543950336)), (5/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((-1065769161/39614081257132168796771975168), (-69573942781/1267650600228229401496703205376)), (29/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((51876083397/20282409603651670423947251286016), (82298199375/20282409603651670423947251286016)), (5/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-8971926653/40564819207303340847894502572032), (-11345668741/40564819207303340847894502572032)), (27/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((23000396951/1298074214633706907132624082305024), (46896646223/2596148429267413814265248164610048)), (33/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((-27657578443/20769187434139310514121985316880384), (-22751568025/20769187434139310514121985316880384)), (5/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/889362867), (-195520/296454289)), 0, by norm_num⟩
  | 1 => ⟨((-59337627852800/263655436399486563), (4284547072000/87885145466495521)), 0, by norm_num⟩
  | 2 => ⟨((73184318431/9007199254740992), (-24251230377/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-20871112087/72057594037927936), (37949310277/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((23482967623/2305843009213693952), (-27727190219/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-26017854667/73786976294838206464), (38740321897/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 6 => ⟨((56637163497/4722366482869645213696), (-52407576703/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-1885895119/4722366482869645213696), (8644321225/18889465931478580854784)), (1/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((31308781587/2417851639229258349412352), (-44715642021/2417851639229258349412352)), (7/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-31366696847/77371252455336267181195264), (56849971023/77371252455336267181195264)), (5/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((7474657545/618970019642690137449562112), (-71208621243/2475880078570760549798248448)), (13/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-26344114417/79228162514264337593543950336), (88004750279/79228162514264337593543950336)), (9/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((20013290907/2535301200456458802993406410752), (-107419488781/2535301200456458802993406410752)), (25/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44797784253/2147483648), (15730524155/4294967296)), (7/4294967296), by norm_num⟩
  | 1 => ⟨((88018545793/68719476736), (3804176145/68719476736)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((42157845919/4398046511104), (-9368827815/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-34042562069/281474976710656), (7656097551/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((40688953417/18014398509481984), (-28025596889/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-14385522069/288230376151711744), (13615661733/576460752303423488)), (21/1152921504606846976), by norm_num⟩
  | 6 => ⟨((44519689703/36893488147419103232), (-13716863303/18446744073709551616)), (29/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-18137216171/590295810358705651712), (28292694377/1180591620717411303424)), (77/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((7604988785/9444732965739290427392), (-59284625681/75557863725914323419136)), (93/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-25824449505/1208925819614629174706176), (62784822135/2417851639229258349412352)), (115/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((10935093735/19342813113834066795298816), (-66976945539/77371252455336267181195264)), (153/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-36351997237/2475880078570760549798248448), (35892600839/1237940039285380274899124224)), (191/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((7238975565/19807040628566084398385987584), (-19286533693/19807040628566084398385987584)), (61/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-78063272993/72057594037927936), (25867979069/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 1 => ⟨((66787558679/576460752303423488), (-15179724111/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-37572748197/4611686018427387904), (22181752175/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((69380945779/147573952589676412928), (-25826881265/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-56637163497/2361183241434822606848), (52407576703/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((42244050665/37778931862957161709568), (-12102049715/9444732965739290427392)), (3/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-29221529481/604462909807314587353088), (41734599219/604462909807314587353088)), (3/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((37640036215/19342813113834066795298816), (-68219965227/19342813113834066795298816)), (11/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((-11211986317/154742504910672534362390528), (53406465931/309485009821345068724781056)), (9/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((6037192887/2475880078570760549798248448), (-80671021087/9903520314283042199192993792)), (15/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-11007309999/158456325028528675187087900672), (59080718829/158456325028528675187087900672)), (3/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((3271880547/2535301200456458802993406410752), (-84226807753/5070602400912917605986812821504)), (19/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((853493237/40564819207303340847894502572032), (117184660095/162259276829213363391578010288128)), (29/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89595563853/4294967296), (15730525697/4294967296)), (1/536870912), by norm_num⟩
  | 1 => ⟨((88018553755/68719476736), (1902086263/34359738368)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((42157810087/4398046511104), (-9368785507/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-68084859471/562949953421312), (15311998059/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((81377042619/36028797018963968), (-28024797213/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-28770399545/576460752303423488), (27229846165/1152921504606846976)), (11/576460752303423488), by norm_num⟩
  | 6 => ⟨((22258953081/18446744073709551616), (-428612177/576460752303423488)), (15/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-72544269953/2361183241434822606848), (28288530561/1180591620717411303424)), (39/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((60834435677/75557863725914323419136), (-59271586993/75557863725914323419136)), (47/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-25821501657/1208925819614629174706176), (62765127061/2417851639229258349412352)), (29/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((43735000277/77371252455336267181195264), (-16737024383/19342813113834066795298816)), (77/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-36348802041/2475880078570760549798248448), (71744075307/2475880078570760549798248448)), (3/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((28957569239/79228162514264337593543950336), (-19272228925/19807040628566084398385987584)), (245/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((28626855769/18446744073709551616), (-33800765219/36893488147419103232)), (3/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-39646254731/147573952589676412928), (7379108933/36893488147419103232)), (3/147573952589676412928), by norm_num⟩
  | 2 => ⟨((32364093427/1180591620717411303424), (-29947186687/1180591620717411303424)), (7/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-40232429205/18889465931478580854784), (46103046533/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((41745042115/302231454903657293676544), (-14905214007/75557863725914323419136)), (1/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-37640036215/4835703278458516698824704), (68219965227/4835703278458516698824704)), (5/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((7474657545/19342813113834066795298816), (-71208621241/77371252455336267181195264)), (3/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((-10349473521/618970019642690137449562112), (69146589503/1237940039285380274899124224)), (3/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((11793546427/19807040628566084398385987584), (-31650385087/9903520314283042199192993792)), (13/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((-2142302739/158456325028528675187087900672), (13787126269/79228162514264337593543950336)), (13/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-670601829/2535301200456458802993406410752), (-92073661503/10141204801825835211973625643008)), (23/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((632033915/10141204801825835211973625643008), (74015586287/162259276829213363391578010288128)), (5/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((-7110898073/1298074214633706907132624082305024), (-57505310695/2596148429267413814265248164610048)), (9/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22398890965/1073741824), (15730525693/4294967296)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((88018553737/68719476736), (951043135/17179869184)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((84315620415/8796093022208), (-4684392865/4398046511104)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-34042430335/281474976710656), (15311999433/562949953421312)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((81377047595/36028797018963968), (-875775135/1125899906842624)), (19/36028797018963968), by norm_num⟩
  | 5 => ⟨((-449537563/9007199254740992), (13614931215/576460752303423488)), (23/1152921504606846976), by norm_num⟩
  | 6 => ⟨((44517920419/36893488147419103232), (-27431213283/36893488147419103232)), (31/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-72544309433/2361183241434822606848), (56577193009/2361183241434822606848)), (79/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((30417240333/37778931862957161709568), (-29635914233/37778931862957161709568)), (95/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-51643036003/2417851639229258349412352), (62765547811/2417851639229258349412352)), (117/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((10933744953/19342813113834066795298816), (-33474399999/38685626227668133590597632)), (155/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-4543580967/309485009821345068724781056), (71745204695/2475880078570760549798248448)), (193/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((3619641903/9903520314283042199192993792), (-77090670623/79228162514264337593543950336)), (123/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-51782549483/9444732965739290427392), (11978874675/2361183241434822606848)), (3/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((48278915045/37778931862957161709568), (-1728864245/1180591620717411303424)), (7/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-25047025269/151115727451828646838272), (71545027233/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((37640036215/2417851639229258349412352), (-68219965227/2417851639229258349412352)), (5/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((-22423972635/19342813113834066795298816), (53406465931/19342813113834066795298816)), (9/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((10866947197/154742504910672534362390528), (-36301959489/154742504910672534362390528)), (13/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((-8255482499/2475880078570760549798248448), (22155269561/1237940039285380274899124224)), (1/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((7712289861/79228162514264337593543950336), (-49633654569/39614081257132168796771975168)), (23/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((3017708231/1267650600228229401496703205376), (103582869191/1267650600228229401496703205376)), (25/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((-3476186533/5070602400912917605986812821504), (-101771431145/20282409603651670423947251286016)), (7/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((11732981821/162259276829213363391578010288128), (94883762647/324518553658426726783156020576256)), (15/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((-30730096973/5192296858534827628530496329220096), (-42209416037/2596148429267413814265248164610048)), (15/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((35275882693/83076749736557242056487941267521536), (17990837729/20769187434139310514121985316880384)), (31/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22398890965/1073741824), (15730525693/4294967296)), (5/2147483648), by norm_num⟩
  | 1 => ⟨((88018553737/68719476736), (951043135/17179869184)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((42157810207/4398046511104), (-146387277/137438953472)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-68084860661/562949953421312), (15311999417/562949953421312)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((81377047553/36028797018963968), (-28024804221/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-57540807983/1152921504606846976), (1701866385/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((5564740037/4611686018427387904), (-27431212623/36893488147419103232)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-72544309203/2361183241434822606848), (56577190051/2361183241434822606848)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((30417240423/37778931862957161709568), (-14817955573/18889465931478580854784)), (3/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-51643037661/2417851639229258349412352), (62765535679/2417851639229258349412352)), (59/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((43734985407/77371252455336267181195264), (-2092149293/2417851639229258349412352)), (39/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-36348662389/2475880078570760549798248448), (71745164441/2475880078570760549798248448)), (97/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((14478584433/39614081257132168796771975168), (-77090601993/79228162514264337593543950336)), (247/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((40480040839/1208925819614629174706176), (-28907081711/604462909807314587353088)), (9/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((-22812143161/2417851639229258349412352), (82690866941/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 2 => ⟨((13590286445/9671406556917033397649408), (-16183777555/4835703278458516698824704)), (11/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((-21953428681/154742504910672534362390528), (36668645949/77371252455336267181195264)), (7/77371252455336267181195264), by norm_num⟩
  | 4 => ⟨((97721147/9671406556917033397649408), (-8392147561/154742504910672534362390528)), (7/618970019642690137449562112), by norm_num⟩
  | 5 => ⟨((-1022462671/2475880078570760549798248448), (105283509691/19807040628566084398385987584)), (23/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((-533433273/39614081257132168796771975168), (-73240412559/158456325028528675187087900672)), (9/79228162514264337593543950336), by norm_num⟩
  | 7 => ⟨((12640678301/2535301200456458802993406410752), (92519482859/2535301200456458802993406410752)), (25/2535301200456458802993406410752), by norm_num⟩
  | 8 => ⟨((-13332933887/20282409603651670423947251286016), (-53911228777/20282409603651670423947251286016)), (17/20282409603651670423947251286016), by norm_num⟩
  | 9 => ⟨((666885785/10141204801825835211973625643008), (58624188941/324518553658426726783156020576256)), (21/324518553658426726783156020576256), by norm_num⟩
  | 10 => ⟨((-29396568911/5192296858534827628530496329220096), (-59969459097/5192296858534827628530496329220096)), (13/2596148429267413814265248164610048), by norm_num⟩
  | 11 => ⟨((36584786087/83076749736557242056487941267521536), (58039501487/83076749736557242056487941267521536)), (29/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((-42182061031/1329227995784915872903807060280344576), (-26671177205/664613997892457936451903530140172288)), (31/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22398890965/1073741824), (15730525693/4294967296)), (11/4294967296), by norm_num⟩
  | 1 => ⟨((88018553737/68719476736), (951043135/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((42157810207/4398046511104), (-146387277/137438953472)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((-68084860661/562949953421312), (15311999417/562949953421312)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((81377047553/36028797018963968), (-28024804223/36028797018963968)), (21/36028797018963968), by norm_num⟩
  | 5 => ⟨((-57540807983/1152921504606846976), (13614931083/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((5564740037/4611686018427387904), (-857225395/1152921504606846976)), (33/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-72544309191/2361183241434822606848), (56577190137/2361183241434822606848)), (81/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((15208620199/18889465931478580854784), (-59271822493/75557863725914323419136)), (97/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-25821518751/1208925819614629174706176), (15691384029/604462909807314587353088)), (119/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((43734984969/77371252455336267181195264), (-33474389135/38685626227668133590597632)), (157/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-36348661299/2475880078570760549798248448), (71745166171/2475880078570760549798248448)), (195/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((1809822897/4951760157141521099596496896), (-19272651293/19807040628566084398385987584)), (31/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-343988569/1208925819614629174706176), (52433068029/77371252455336267181195264)), (5/38685626227668133590597632), by norm_num⟩
  | 1 => ⟨((13336104807/154742504910672534362390528), (-89100780135/309485009821345068724781056)), (17/309485009821345068724781056), by norm_num⟩
  | 2 => ⟨((-1899613189/154742504910672534362390528), (81567985437/1237940039285380274899124224)), (17/1237940039285380274899124224), by norm_num⟩
  | 3 => ⟨((8281573107/9903520314283042199192993792), (-106594732889/9903520314283042199192993792)), (3/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((3240460587/79228162514264337593543950336), (55614423163/39614081257132168796771975168)), (7/19807040628566084398385987584), by norm_num⟩
  | 5 => ⟨((-6719006697/316912650057057350374175801344), (-49177663581/316912650057057350374175801344)), (27/633825300114114700748351602688), by norm_num⟩
  | 6 => ⟨((9449289555/2535301200456458802993406410752), (2387990967/158456325028528675187087900672)), (13/2535301200456458802993406410752), by norm_num⟩
  | 7 => ⟨((-303836095/633825300114114700748351602688), (-53418876341/40564819207303340847894502572032)), (21/40564819207303340847894502572032), by norm_num⟩
  | 8 => ⟨((16741507515/324518553658426726783156020576256), (68305872917/649037107316853453566312041152512)), (29/649037107316853453566312041152512), by norm_num⟩
  | 9 => ⟨((-12732644645/2596148429267413814265248164610048), (-40399107217/5192296858534827628530496329220096)), (5/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((1101050295/2596148429267413814265248164610048), (22277760213/41538374868278621028243970633760768)), (7/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((-22581186697/664613997892457936451903530140172288), (-46041897715/1329227995784915872903807060280344576)), (33/1329227995784915872903807060280344576), by norm_num⟩
  | 12 => ⟨((54306970765/21267647932558653966460912964485513216), (22336892981/10633823966279326983230456482242756608)), (41/21267647932558653966460912964485513216), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22398890965/1073741824), (15730525693/4294967296)), (3/1073741824), by norm_num⟩
  | 1 => ⟨((88018553737/68719476736), (951043135/17179869184)), (9/68719476736), by norm_num⟩
  | 2 => ⟨((42157810207/4398046511104), (-146387277/137438953472)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-68084860661/562949953421312), (15311999417/562949953421312)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((81377047553/36028797018963968), (-28024804223/36028797018963968)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-57540807983/1152921504606846976), (13614931083/576460752303423488)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((5564740037/4611686018427387904), (-27431212639/36893488147419103232)), (17/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-9068038649/295147905179352825856), (28288595067/1180591620717411303424)), (41/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((1901077525/2361183241434822606848), (-59271822485/75557863725914323419136)), (49/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-25821518757/1208925819614629174706176), (62765536097/2417851639229258349412352)), (15/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((21867492501/38685626227668133590597632), (-66948778229/77371252455336267181195264)), (79/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-36348661383/2475880078570760549798248448), (71745166085/2475880078570760549798248448)), (49/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((14478583277/39614081257132168796771975168), (-38545302503/39614081257132168796771975168)), (249/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-65209608482663/65536), (-299354682626453/524288)), (9824873/1048576), by norm_num⟩
  | 1 => ⟨((-79542499811/64), (-50330077945/64)), (51/4), by norm_num⟩
  | 2 => ⟨((-50196806291/64), (-8679115023/16)), (561/64), by norm_num⟩
  | 3 => ⟨((-21326072705/64), (-8005392511/32)), (65/16), by norm_num⟩
  | 4 => ⟨((-27432936689/256), (-347418515/4)), (365/256), by norm_num⟩
  | 5 => ⟨((-28477867103/1024), (-24808550397/1024)), (829/2048), by norm_num⟩
  | 6 => ⟨((-24839477551/4096), (-46347870825/8192)), (793/8192), by norm_num⟩
  | 7 => ⟨((-37433053923/32768), (-37289697267/32768)), (657/32768), by norm_num⟩
  | 8 => ⟨((-49727667255/262144), (-26382763797/131072)), (963/262144), by norm_num⟩
  | 9 => ⟨((-29567841933/1048576), (-66704115059/2097152)), (317/524288), by norm_num⟩
  | 10 => ⟨((-31858429485/8388608), (-38139092399/8388608)), (95/1048576), by norm_num⟩
  | 11 => ⟨((-31405468769/67108864), (-19924784397/33554432)), (837/67108864), by norm_num⟩
  | 12 => ⟨((-57103417889/1073741824), (-38359405309/536870912)), (1707/1073741824), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((805574509163673/5070602400912917605986812821504), (-3413672138425/10141204801825835211973625643008)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1814785802075233/633825300114114700748351602688), (-4192820087113/633825300114114700748351602688)), (2245/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1930305526091853/39614081257132168796771975168), (-4729843089785/39614081257132168796771975168)), (5067/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1932657481737387/2475880078570760549798248448), (-1259105759725/618970019642690137449562112)), (5397/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1814370483271299/154742504910672534362390528), (-1262171936775/38685626227668133590597632)), (5411/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1590084259497565/9671406556917033397649408), (-2373107827593/4835703278458516698824704)), (5089/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1294303057066567/604462909807314587353088), (-4166056965755/604462909807314587353088)), (4469/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1945596704155469/75557863725914323419136), (-3397270263431/37778931862957161709568)), (7291/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1340975277098097/4722366482869645213696), (-2558808901161/2361183241434822606848)), (5495/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((840653316431805/295147905179352825856), (-3536099427943/295147905179352825856)), (7599/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1898499992457485/73786976294838206464), (-8893797729949/73786976294838206464)), (9563/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1907339852778967/9223372036854775808), (-5039852538513/4611686018427387904)), (339/288230376151711744), by norm_num⟩
  | 6 => ⟨((419734920372025/288230376151711744), (-10173269128365/1152921504606846976)), (5481/576460752303423488), by norm_num⟩
  | 5 => ⟨((1269313448660289/144115188075855872), (-9008030628631/144115188075855872)), (9721/144115188075855872), by norm_num⟩
  | 4 => ⟨((802269907061777/18014398509481984), (-13727822270157/36028797018963968)), (3711/9007199254740992), by norm_num⟩
  | 3 => ⟨((815903992699231/4503599627370496), (-17544088792515/9007199254740992)), (1189/562949953421312), by norm_num⟩
  | 2 => ⟨((1258690942890807/2251799813685248), (-1133387765689/140737488355328)), (19747/2251799813685248), by norm_num⟩
  | 1 => ⟨((665330875525759/562949953421312), (-28725485644581/1125899906842624)), (15747/562949953421312), by norm_num⟩
  | 0 => ⟨((97403035074865/70368744177664), (-31925093167369/562949953421312)), (70901/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((97403035074865/70368744177664), (-31925093167369/562949953421312)), (270465855125045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((538388238792073/281474976710656), (-88380175201041/562949953421312)), (51081/281474976710656), by norm_num⟩
  | 2 => ⟨((1022858710895095/281474976710656), (-169048230953533/281474976710656)), (211449/281474976710656), by norm_num⟩
  | 3 => ⟨((451932996832419/35184372088832), (-307154223108745/70368744177664)), (111923/17592186044416), by norm_num⟩
  | 4 => ⟨((40114024198467/274877906944), (-61645412569819/549755813888)), (481539/2199023255552), by norm_num⟩
  | 5 => ⟨((299722030226529/34359738368), (-562259986406889/17179869184)), (3883407/34359738368), by norm_num⟩
  | 6 => ⟨((-65209608482663/65536), (-299354682626453/524288)), (9824873/1048576), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((22398890965/1073741824), (15730525693/4294967296)), (3/1073741824), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/6457489), (-2346240/6457489)), 0, by norm_num⟩
  | 1 => ⟨((214867148800/41699164185121), (5285609472000/41699164185121)), 0, by norm_num⟩
  | 2 => ⟨((-52614493565/2199023255552), (-46562791953/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((70546745367/8796093022208), (-2872567289/4398046511104)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((-45047926031/35184372088832), (55272950531/35184372088832)), (1/8796093022208), by norm_num⟩
  | 5 => ⟨((-8733933481/140737488355328), (-17825206433/35184372088832)), (7/140737488355328), by norm_num⟩
  | 6 => ⟨((28953151095/281474976710656), (43402194295/562949953421312)), (11/562949953421312), by norm_num⟩
  | 7 => ⟨((-35971146357/1125899906842624), (2948949595/562949953421312)), (17/2251799813685248), by norm_num⟩
  | 8 => ⟨((41624793487/9007199254740992), (-60508801315/9007199254740992)), (25/9007199254740992), by norm_num⟩
  | 9 => ⟨((14927113381/36028797018963968), (72466552579/36028797018963968)), (9/9007199254740992), by norm_num⟩
  | 10 => ⟨((-63074586839/144115188075855872), (-9928786495/36028797018963968)), (53/144115188075855872), by norm_num⟩
  | 11 => ⟨((72869096125/576460752303423488), (-18124022437/576460752303423488)), (19/144115188075855872), by norm_num⟩
  | 12 => ⟨((-18836453821/1152921504606846976), (8199711445/288230376151711744)), (109/2305843009213693952), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (1833/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (1833/1280)))⁻¹=value ((2252800/6457489), (-2346240/6457489)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/6457489), (-2346240/6457489))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/12601489), (-2346240/12601489)), 0, by norm_num⟩
  | 1 => ⟨((-4818297651200/158797525017121), (9129689088000/158797525017121)), 0, by norm_num⟩
  | 2 => ⟨((-2935732395/4398046511104), (-102925131721/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((41952836659/35184372088832), (61377890661/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-24382367845/70368744177664), (-11141717035/70368744177664)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((19206906729/281474976710656), (-4397016069/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 6 => ⟨((-22086179807/2251799813685248), (34039689949/4503599627370496)), (1/562949953421312), by norm_num⟩
  | 7 => ⟨((14604338199/18014398509481984), (-74941683019/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 8 => ⟨((9867781937/144115188075855872), (28579451355/72057594037927936)), (17/144115188075855872), by norm_num⟩
  | 9 => ⟨((-54757343983/1152921504606846976), (-63251108669/1152921504606846976)), (17/576460752303423488), by norm_num⟩
  | 10 => ⟨((57370054937/4611686018427387904), (18672212991/4611686018427387904)), (17/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-42383539085/18446744073709551616), (9831632199/18446744073709551616)), (69/36893488147419103232), by norm_num⟩
  | 12 => ⟨((22514078861/73786976294838206464), (-5463592515/18446744073709551616)), (69/147573952589676412928), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (1833/1280)))⁻¹=value ((3891200/12601489), (-2346240/12601489)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/12601489), (-2346240/12601489))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3261253222400/81373976601121), (-14415298560000/81373976601121)), 0, by norm_num⟩
  | 1 => ⟨((39027374529/1099511627776), (38077805349/549755813888)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-6393328421/274877906944), (-10415754511/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((30029268101/4398046511104), (-5272401811/2199023255552)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((-8214185527/8796093022208), (60843809049/35184372088832)), (5/35184372088832), by norm_num⟩
  | 5 => ⟨((-9168693423/70368744177664), (-70201571715/140737488355328)), (1/17592186044416), by norm_num⟩
  | 6 => ⟨((31713923571/281474976710656), (39147233051/562949953421312)), (3/140737488355328), by norm_num⟩
  | 7 => ⟨((-73767834989/2251799813685248), (16479653569/2251799813685248)), (19/2251799813685248), by norm_num⟩
  | 8 => ⟨((10252014279/2251799813685248), (-32040616367/4503599627370496)), (27/9007199254740992), by norm_num⟩
  | 9 => ⟨((16638280381/36028797018963968), (74443149725/36028797018963968)), (39/36028797018963968), by norm_num⟩
  | 10 => ⟨((-2027106283/4503599627370496), (-10074663159/36028797018963968)), (55/144115188075855872), by norm_num⟩
  | 11 => ⟨((37096790861/288230376151711744), (-18431260943/576460752303423488)), (39/288230376151711744), by norm_num⟩
  | 12 => ⟨((-38376472607/2305843009213693952), (66280640625/2305843009213693952)), (111/2305843009213693952), by norm_num⟩
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
  | 0 => ⟨((27/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/2446921), (-782080/7340763)), 0, by norm_num⟩
  | 1 => ⟨((-1392868556800/53886801422169), (160169984000/5987422380241)), 0, by norm_num⟩
  | 2 => ⟨((32019290405/17592186044416), (-83305945753/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((1671204473/70368744177664), (24328692515/35184372088832)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-22414199597/562949953421312), (-48157542475/562949953421312)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((21517355489/2251799813685248), (38815738947/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-59764137537/36028797018963968), (-5161395793/9007199254740992)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((34411615249/144115188075855872), (-4733239737/288230376151711744)), (11/288230376151711744), by norm_num⟩
  | 8 => ⟨((-67106488151/2305843009213693952), (34083421351/2305843009213693952)), (17/2305843009213693952), by norm_num⟩
  | 9 => ⟨((52874458303/18446744073709551616), (-62830092451/18446744073709551616)), (25/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-3291213927/18446744073709551616), (85637137587/147573952589676412928)), (37/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-5025136619/590295810358705651712), (-1519241875/18446744073709551616)), (27/590295810358705651712), by norm_num⟩
  | 12 => ⟨((25765021841/4722366482869645213696), (46686412909/4722366482869645213696)), (5/590295810358705651712), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (1833/1280)))⁻¹=value ((614400/2446921), (-782080/7340763)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/2446921), (-782080/7340763))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4843484021/549755813888), (-107203006741/2199023255552)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((43968965725/2199023255552), (42354901279/2199023255552)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-91352699739/8796093022208), (-5513469311/4398046511104)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((12444806899/4398046511104), (-30351906781/17592186044416)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((-5516611415/17592186044416), (31702410581/35184372088832)), (7/70368744177664), by norm_num⟩
  | 5 => ⟨((-26596005493/281474976710656), (-2121541433/8796093022208)), (5/140737488355328), by norm_num⟩
  | 6 => ⟨((68015577445/1125899906842624), (17284842285/562949953421312)), (15/1125899906842624), by norm_num⟩
  | 7 => ⟨((-2345490493/140737488355328), (10563265161/2251799813685248)), (23/4503599627370496), by norm_num⟩
  | 8 => ⟨((20064593013/9007199254740992), (-67520525789/18014398509481984)), (33/18014398509481984), by norm_num⟩
  | 9 => ⟨((18452717807/72057594037927936), (76297031847/72057594037927936)), (47/72057594037927936), by norm_num⟩
  | 10 => ⟨((-33342963941/144115188075855872), (-40798529275/288230376151711744)), (33/144115188075855872), by norm_num⟩
  | 11 => ⟨((75513159959/1152921504606846976), (-9392987879/576460752303423488)), (93/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-19533728497/2305843009213693952), (33493192895/2305843009213693952)), (133/4611686018427387904), by norm_num⟩
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
  | 0 => ⟨((35/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/34719889), (-2346240/34719889)), 0, by norm_num⟩
  | 1 => ⟨((-22937690931200/1205470692172321), (16817848320000/1205470692172321)), 0, by norm_num⟩
  | 2 => ⟨((26261600431/17592186044416), (-73291021745/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-23563206313/281474976710656), (74721676519/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-738933637/2251799813685248), (-68075092575/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((9505628403/9007199254740992), (56017292903/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((-30841423725/144115188075855872), (-41120751781/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 7 => ⟨((73168546805/2305843009213693952), (51242598561/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((-18568595595/4611686018427387904), (-88042105/72057594037927936)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((67428805139/147573952589676412928), (-732004639/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-55287591283/1180591620717411303424), (9717668065/590295810358705651712)), (19/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((40403526783/9444732965739290427392), (-15497195141/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-49975321459/151115727451828646838272), (73033450129/151115727451828646838272)), (49/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (1833/1280)))⁻¹=value ((7168000/34719889), (-2346240/34719889)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/34719889), (-2346240/34719889))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-44976682545/8796093022208), (-83292345609/8796093022208)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((55215775209/8796093022208), (30170299961/8796093022208)), (3/8796093022208), by norm_num⟩
  | 2 => ⟨((-105296962999/35184372088832), (5296021387/17592186044416)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((53926892995/70368744177664), (-47822780773/70368744177664)), (7/70368744177664), by norm_num⟩
  | 4 => ⟨((-4221830283/70368744177664), (42679773461/140737488355328)), (11/281474976710656), by norm_num⟩
  | 5 => ⟨((-22438876577/562949953421312), (-43201148837/562949953421312)), (17/1125899906842624), by norm_num⟩
  | 6 => ⟨((95719956547/4503599627370496), (9943392263/1125899906842624)), (25/4503599627370496), by norm_num⟩
  | 7 => ⟨((-25292442911/4503599627370496), (17124258027/9007199254740992)), (19/9007199254740992), by norm_num⟩
  | 8 => ⟨((26016298003/36028797018963968), (-1475326567/1125899906842624)), (7/9007199254740992), by norm_num⟩
  | 9 => ⟨((1696163629/18014398509481984), (52019037579/144115188075855872)), (39/144115188075855872), by norm_num⟩
  | 10 => ⟨((-45682278895/576460752303423488), (-6869524729/144115188075855872)), (55/576460752303423488), by norm_num⟩
  | 11 => ⟨((102433819733/4611686018427387904), (-25581700179/4611686018427387904)), (153/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-26496732161/9223372036854775808), (5642817721/1152921504606846976)), (109/9223372036854775808), by norm_num⟩
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
  | 0 => ⟨((43/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/50694289), (-2346240/50694289)), 0, by norm_num⟩
  | 1 => ⟨((-36023919411200/2569910937215521), (20661927936000/2569910937215521)), 0, by norm_num⟩
  | 2 => ⟨((18146067049/17592186044416), (-1124485919/1099511627776)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-9278244607/140737488355328), (63444714447/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((28086036501/9007199254740992), (-50956074189/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((-162276915/18014398509481984), (19003634231/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-27242839195/1152921504606846976), (-26469939457/288230376151711744)), (11/1152921504606846976), by norm_num⟩
  | 7 => ⟨((19265707113/4611686018427387904), (34264264375/4611686018427387904)), (11/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-39460651793/73786976294838206464), (-5060586709/9223372036854775808)), (11/73786976294838206464), by norm_num⟩
  | 9 => ⟨((34914630453/590295810358705651712), (41652068017/1180591620717411303424)), (21/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-28116388073/4722366482869645213696), (-16015103135/9444732965739290427392)), (19/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((42038944105/75557863725914323419136), (1436030089/151115727451828646838272)), (17/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-14672121863/302231454903657293676544), (7283686297/604462909807314587353088)), (31/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (1833/1280)))⁻¹=value ((8806400/50694289), (-2346240/50694289)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/50694289), (-2346240/50694289))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-46672436031/35184372088832), (-49550324749/35184372088832)), (3/35184372088832), by norm_num⟩
  | 1 => ⟨((98306632403/70368744177664), (27932010187/70368744177664)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((-89576274149/140737488355328), (26551104139/140737488355328)), (9/140737488355328), by norm_num⟩
  | 3 => ⟨((10737607521/70368744177664), (-51971829825/281474976710656)), (9/281474976710656), by norm_num⟩
  | 4 => ⟨((-3021747171/562949953421312), (42235936753/562949953421312)), (7/562949953421312), by norm_num⟩
  | 5 => ⟨((-3306175683/281474976710656), (-40818622081/2251799813685248)), (21/4503599627370496), by norm_num⟩
  | 6 => ⟨((99810918909/18014398509481984), (16691759029/9007199254740992)), (31/18014398509481984), by norm_num⟩
  | 7 => ⟨((-25431593479/18014398509481984), (20083941813/36028797018963968)), (3/4503599627370496), by norm_num⟩
  | 8 => ⟨((6287548311/36028797018963968), (-6163384811/18014398509481984)), (35/144115188075855872), by norm_num⟩
  | 9 => ⟨((14885124343/576460752303423488), (106185802445/1152921504606846976)), (3/36028797018963968), by norm_num⟩
  | 10 => ⟨((-46915987673/2305843009213693952), (-6926187797/576460752303423488)), (17/576460752303423488), by norm_num⟩
  | 11 => ⟨((26042683647/4611686018427387904), (-26173682461/18446744073709551616)), (47/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-26939163817/36893488147419103232), (5705152883/4611686018427387904)), (67/18446744073709551616), by norm_num⟩
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
  | 0 => ⟨((51/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/23315163), (-782080/23315163)), 0, by norm_num⟩
  | 1 => ⟨((-1918314905600/181198941905523), (2722889728000/543596825716569)), 0, by norm_num⟩
  | 2 => ⟨((49711262725/70368744177664), (-2425759389/4398046511104)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-48970886751/1125899906842624), (59705888935/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((21239784203/9007199254740992), (-42233661249/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((-3510018857/36028797018963968), (56152959491/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((851946873/1152921504606846976), (-35424604315/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 7 => ⟨((16976925315/36893488147419103232), (85095244151/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-21558185413/295147905179352825856), (-48550428455/295147905179352825856)), (9/295147905179352825856), by norm_num⟩
  | 9 => ⟨((38782417235/4722366482869645213696), (52214242229/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-60342045529/75557863725914323419136), (-25984489643/37778931862957161709568)), (21/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((86031829169/1208925819614629174706176), (717038153/18889465931478580854784)), (1/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-14386277855/2417851639229258349412352), (-15867508915/9671406556917033397649408)), (25/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (1833/1280)))⁻¹=value ((3481600/23315163), (-782080/23315163)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/23315163), (-782080/23315163))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-69052769227/281474976710656), (-46669313657/281474976710656)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((68405885933/281474976710656), (2910065195/140737488355328)), (5/281474976710656), by norm_num⟩
  | 2 => ⟨((-60352501685/562949953421312), (1831479947/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((13355381717/562949953421312), (-43206532769/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 4 => ⟨((5291018045/9007199254740992), (65962683603/4503599627370496)), (27/9007199254740992), by norm_num⟩
  | 5 => ⟨((-11941529465/4503599627370496), (-3824233043/1125899906842624)), (21/18014398509481984), by norm_num⟩
  | 6 => ⟨((20616985799/18014398509481984), (21617703189/72057594037927936)), (15/36028797018963968), by norm_num⟩
  | 7 => ⟨((-81452508339/288230376151711744), (36718222033/288230376151711744)), (23/144115188075855872), by norm_num⟩
  | 8 => ⟨((19338136189/576460752303423488), (-82082933749/1152921504606846976)), (67/1152921504606846976), by norm_num⟩
  | 9 => ⟨((12992741733/2305843009213693952), (43270357091/2305843009213693952)), (47/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-77047967363/18446744073709551616), (-44609308369/18446744073709551616)), (33/4611686018427387904), by norm_num⟩
  | 11 => ⟨((84713976307/73786976294838206464), (-10728562705/36893488147419103232)), (91/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-43795036845/295147905179352825856), (73844689677/295147905179352825856)), (129/147573952589676412928), by norm_num⟩
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
  | 0 => ⟨((59/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/92473489), (-2346240/92473489)), 0, by norm_num⟩
  | 1 => ⟨((-70249440051200/8551346167833121), (28350087168000/8551346167833121)), 0, by norm_num⟩
  | 2 => ⟨((69616722201/140737488355328), (-11287635571/35184372088832)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-63608178069/2251799813685248), (61327896545/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((27021814793/18014398509481984), (-77019028989/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-5107570435/72057594037927936), (22870028329/144115188075855872)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((24144611615/9223372036854775808), (-811882145/72057594037927936)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-4145686727/147573952589676412928), (14191594397/18446744073709551616)), (11/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-9355413405/1180591620717411303424), (-3735032003/73786976294838206464)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((5477371683/4722366482869645213696), (30285357743/9444732965739290427392)), (11/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-35197127305/302231454903657293676544), (-14717367379/75557863725914323419136)), (15/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((48741825481/4835703278458516698824704), (6799253201/604462909807314587353088)), (5/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-7749017281/9671406556917033397649408), (-23483222077/38685626227668133590597632)), (13/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (1833/1280)))⁻¹=value ((12083200/92473489), (-2346240/92473489)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/92473489), (-2346240/92473489))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-81655907379/2251799813685248), (-34768908223/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((19616054015/562949953421312), (-6565113515/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 2 => ⟨((-16806650815/1125899906842624), (22865433453/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 3 => ⟨((26775735839/9007199254740992), (-58268043325/9007199254740992)), (7/4503599627370496), by norm_num⟩
  | 4 => ⟨((189275953/562949953421312), (42501045043/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-8728776579/18014398509481984), (-37932675457/72057594037927936)), (17/72057594037927936), by norm_num⟩
  | 6 => ⟨((112693025583/576460752303423488), (11070670715/288230376151711744)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((-54133028523/1152921504606846976), (27423964095/1152921504606846976)), (37/1152921504606846976), by norm_num⟩
  | 8 => ⟨((24639510521/4611686018427387904), (-28370455067/2305843009213693952)), (53/4611686018427387904), by norm_num⟩
  | 9 => ⟨((9402368473/9223372036854775808), (58673316073/18446744073709551616)), (75/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-26344667977/36893488147419103232), (-29875402033/73786976294838206464)), (105/73786976294838206464), by norm_num⟩
  | 11 => ⟨((57384995015/295147905179352825856), (-14678617453/295147905179352825856)), (145/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-29647599029/1180591620717411303424), (12447195997/295147905179352825856)), (51/295147905179352825856), by norm_num⟩
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
  | 0 => ⟨((67/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/118278289), (-2346240/118278289)), 0, by norm_num⟩
  | 1 => ⟨((-91388732211200/13989753648767521), (32194166784000/13989753648767521)), 0, by norm_num⟩
  | 2 => ⟨((12529137381/35184372088832), (-13952583641/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-42084276431/2251799813685248), (33851622357/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((33685950735/36028797018963968), (-38095798567/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-50436070163/1152921504606846976), (40702018249/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((33890931497/18446744073709551616), (-41777024775/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-18194375633/295147905179352825856), (2591370563/9223372036854775808)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((3726578903/4722366482869645213696), (-79848052725/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((9212718331/75557863725914323419136), (74697495075/75557863725914323419136)), (1/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-20404183337/1208925819614629174706176), (-67863944171/1208925819614629174706176)), (9/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29706425155/19342813113834066795298816), (59745793937/19342813113834066795298816)), (21/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-18525721317/154742504910672534362390528), (-25367613599/154742504910672534362390528)), (3/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (1833/1280)))⁻¹=value ((13721600/118278289), (-2346240/118278289)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/118278289), (-2346240/118278289))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-81301541447/18014398509481984), (-19310437941/18014398509481984)), (5/9007199254740992), by norm_num⟩
  | 1 => ⟨((9585927809/2251799813685248), (-18230982043/18014398509481984)), (5/9007199254740992), by norm_num⟩
  | 2 => ⟨((-63670075899/36028797018963968), (3546682505/2251799813685248)), (15/36028797018963968), by norm_num⟩
  | 3 => ⟨((10932160183/36028797018963968), (-4135833259/4503599627370496)), (9/36028797018963968), by norm_num⟩
  | 4 => ⟨((22284081545/288230376151711744), (23297071159/72057594037927936)), (29/288230376151711744), by norm_num⟩
  | 5 => ⟨((-42857718381/576460752303423488), (-20016483359/288230376151711744)), (23/576460752303423488), by norm_num⟩
  | 6 => ⟨((65583607789/2305843009213693952), (8921017709/2305843009213693952)), (33/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-61459075247/9223372036854775808), (1080451469/288230376151711744)), (49/9223372036854775808), by norm_num⟩
  | 8 => ⟨((26751481917/36893488147419103232), (-33515530339/18446744073709551616)), (71/36893488147419103232), by norm_num⟩
  | 9 => ⟨((2901988335/18446744073709551616), (68083909979/147573952589676412928)), (101/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-61729131033/590295810358705651712), (-17120775615/295147905179352825856)), (141/590295810358705651712), by norm_num⟩
  | 11 => ⟨((33305004051/1180591620717411303424), (-17233844815/2361183241434822606848)), (195/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-34385776147/9444732965739290427392), (57554563287/9444732965739290427392)), (273/9444732965739290427392), by norm_num⟩
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
  | 0 => ⟨((75/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/49119963), (-782080/49119963)), 0, by norm_num⟩
  | 1 => ⟨((-4267125145600/804256921707123), (4004249600000/2412770765121369)), 0, by norm_num⟩
  | 2 => ⟨((74113891765/281474976710656), (-9058726229/70368744177664)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-28593224421/2251799813685248), (2478480141/281474976710656)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((2664707851/4503599627370496), (-40352061513/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((-15206389865/576460752303423488), (19539655631/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((1273924865/1152921504606846976), (-72922302627/36893488147419103232)), (9/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-1544064431/36893488147419103232), (16500181261/147573952589676412928)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((6097065761/4722366482869645213696), (-29091636147/4722366482869645213696)), (11/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-2757327777/151115727451828646838272), (50070907509/151115727451828646838272)), (11/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-4078494461/2417851639229258349412352), (-42104184379/2417851639229258349412352)), (11/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((4381984747/19342813113834066795298816), (34590207663/38685626227668133590597632)), (11/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-23427976415/1237940039285380274899124224), (-27727665507/618970019642690137449562112)), (11/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (1833/1280)))⁻¹=value ((5120000/49119963), (-782080/49119963)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/49119963), (-782080/49119963))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-35127567137/72057594037927936), (-718346077/18014398509481984)), (5/72057594037927936), by norm_num⟩
  | 1 => ⟨((32666479137/72057594037927936), (-25230219727/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 2 => ⟨((-6534140597/36028797018963968), (59099981715/288230376151711744)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1788878919/72057594037927936), (-64957918185/576460752303423488)), (5/144115188075855872), by norm_num⟩
  | 4 => ⟨((29537097687/2305843009213693952), (88866567097/2305843009213693952)), (33/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-11332738131/1152921504606846976), (-36716262425/4611686018427387904)), (27/4611686018427387904), by norm_num⟩
  | 6 => ⟨((66444252699/18446744073709551616), (5296044829/18446744073709551616)), (39/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-60865617165/73786976294838206464), (37670928239/73786976294838206464)), (57/73786976294838206464), by norm_num⟩
  | 8 => ⟨((12629203777/147573952589676412928), (-34547262445/147573952589676412928)), (41/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1560374815/73786976294838206464), (69024879111/1180591620717411303424)), (117/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-31619323805/2361183241434822606848), (-34285061171/4722366482869645213696)), (163/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((8453057675/2361183241434822606848), (-8860852169/9444732965739290427392)), (113/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-17437901081/37778931862957161709568), (58221136377/75557863725914323419136)), (79/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((83/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/179718289), (-2346240/179718289)), 0, by norm_num⟩
  | 1 => ⟨((-141720380211200/32298663401087521), (39882326016000/32298663401087521)), 0, by norm_num⟩
  | 2 => ⟨((14034846725/70368744177664), (-1531179097/17592186044416)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-39920234761/4503599627370496), (12200383041/2251799813685248)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((55315911907/144115188075855872), (-45265192461/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((-37128285449/2305843009213693952), (40027990815/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((23913255671/36893488147419103232), (-68331268613/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-14526125713/590295810358705651712), (14174792309/295147905179352825856)), (1/147573952589676412928), by norm_num⟩
  | 8 => ⟨((32122445307/37778931862957161709568), (-91873450919/37778931862957161709568)), (15/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-14710712445/604462909807314587353088), (18218164031/151115727451828646838272)), (7/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((7040515167/19342813113834066795298816), (-113353709467/19342813113834066795298816)), (25/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((6511413617/309485009821345068724781056), (86506518357/309485009821345068724781056)), (11/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-13961791807/4951760157141521099596496896), (-4048544727/309485009821345068724781056)), (5/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (1833/1280)))⁻¹=value ((16998400/179718289), (-2346240/179718289)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/179718289), (-2346240/179718289))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-53760056567/1152921504606846976), (2989101887/1152921504606846976)), (9/1152921504606846976), by norm_num⟩
  | 1 => ⟨((12330809241/288230376151711744), (-26406624139/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-37701414897/2305843009213693952), (53320104305/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 3 => ⟨((3457144321/2305843009213693952), (-112363359459/9223372036854775808)), (39/9223372036854775808), by norm_num⟩
  | 4 => ⟨((7947512351/4611686018427387904), (9370741591/2305843009213693952)), (17/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-42120691797/36893488147419103232), (-14861584829/18446744073709551616)), (27/36893488147419103232), by norm_num⟩
  | 6 => ⟨((59573337761/147573952589676412928), (3181458623/295147905179352825856)), (79/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-26715789231/295147905179352825856), (18057911199/295147905179352825856)), (59/590295810358705651712), by norm_num⟩
  | 8 => ⟨((21060468295/2361183241434822606848), (-31573353863/1180591620717411303424)), (83/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((23764824659/9444732965739290427392), (15529168115/2361183241434822606848)), (119/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-7193608235/4722366482869645213696), (-30467668429/37778931862957161709568)), (83/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((61000315849/151115727451828646838272), (-2026417547/18889465931478580854784)), (115/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-31424741413/604462909807314587353088), (6544493777/75557863725914323419136)), (321/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((91/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1433600/16565653), (-180480/16565653)), 0, by norm_num⟩
  | 1 => ⟨((-77793689600/21109296870493), (258736128000/274420859316409)), 0, by norm_num⟩
  | 2 => ⟨((86878363491/562949953421312), (-267719501/4398046511104)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-14290304875/2251799813685248), (7824207069/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((73692595355/288230376151711744), (-1665602615/9007199254740992)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-11593415603/1152921504606846976), (43323323357/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((28329599339/73786976294838206464), (-68071289391/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-260105657/18446744073709551616), (52065730291/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((37023857149/75557863725914323419136), (-2434261003/2361183241434822606848)), (3/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-18843165667/1208925819614629174706176), (57156467591/1208925819614629174706176)), (5/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((16127792153/38685626227668133590597632), (-82426284291/38685626227668133590597632)), (17/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-7962989003/1237940039285380274899124224), (116942751451/1237940039285380274899124224)), (27/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-4679603875/19807040628566084398385987584), (-20414080717/4951760157141521099596496896)), (11/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (1833/1280)))⁻¹=value ((1433600/16565653), (-180480/16565653)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((1433600/16565653), (-180480/16565653))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-36958854075/9223372036854775808), (6755081239/9223372036854775808)), (15/18446744073709551616), by norm_num⟩
  | 1 => ⟨((4176064837/1152921504606846976), (-46149024443/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-24094085045/18446744073709551616), (85123310661/36893488147419103232)), (27/36893488147419103232), by norm_num⟩
  | 3 => ⟨((23619079/576460752303423488), (-21722188209/18446744073709551616)), (17/36893488147419103232), by norm_num⟩
  | 4 => ⟨((14613975469/73786976294838206464), (56682274773/147573952589676412928)), (31/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-17449372469/147573952589676412928), (-5373440411/73786976294838206464)), (49/590295810358705651712), by norm_num⟩
  | 6 => ⟨((95782704661/2361183241434822606848), (-2262603141/2361183241434822606848)), (9/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-328973387/36893488147419103232), (15450110073/2361183241434822606848)), (27/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((31383558767/37778931862957161709568), (-3238710003/1180591620717411303424)), (75/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((20280142519/75557863725914323419136), (12561105537/18889465931478580854784)), (27/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-23551450783/151115727451828646838272), (-24332076019/302231454903657293676544)), (151/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((24750916437/604462909807314587353088), (-26710284409/2417851639229258349412352)), (13/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-1591853345/302231454903657293676544), (10594092877/1208925819614629174706176)), (145/2417851639229258349412352), by norm_num⟩
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
  | 0 => ⟨((99/8), (1833/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/28251721), (-782080/84755163)), 0, by norm_num⟩
  | 1 => ⟨((-22532160716800/7183437655156569), (1761869824000/2394479218385523)), 0, by norm_num⟩
  | 2 => ⟨((8561421765/70368744177664), (-24662019261/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-83743227457/18014398509481984), (20788494015/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((25176221897/144115188075855872), (-32704822405/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-59413332709/9223372036854775808), (12290078941/2305843009213693952)), (3/4611686018427387904), by norm_num⟩
  | 6 => ⟨((2142003833/9223372036854775808), (-17873179351/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-38448213391/4722366482869645213696), (12666682471/1180591620717411303424)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((41573485127/151115727451828646838272), (-70319370345/151115727451828646838272)), (3/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-21329661649/2417851639229258349412352), (5990906109/302231454903657293676544)), (9/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((20137334641/77371252455336267181195264), (-64296830259/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-16199300553/2475880078570760549798248448), (85005833435/2475880078570760549798248448)), (21/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((8117497813/79228162514264337593543950336), (-110845886505/79228162514264337593543950336)), (31/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (1833/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (1833/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (1833/1280)))⁻¹=value ((2252800/28251721), (-782080/84755163)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/28251721), (-782080/84755163))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-92312849121/295147905179352825856), (28150099747/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
  | 1 => ⟨((40992667009/147573952589676412928), (-35146060659/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-27400942277/295147905179352825856), (61040125379/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
  | 3 => ⟨((-5727678055/1180591620717411303424), (-121543279367/1180591620717411303424)), (53/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((47237176813/2361183241434822606848), (38820790399/1180591620717411303424)), (25/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-52181859005/4722366482869645213696), (-28025512269/4722366482869645213696)), (5/590295810358705651712), by norm_num⟩
  | 6 => ⟨((4360880715/1180591620717411303424), (-5007553937/18889465931478580854784)), (59/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-7524636307/9444732965739290427392), (47727090497/75557863725914323419136)), (11/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((10544550621/151115727451828646838272), (-77152662123/302231454903657293676544)), (123/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((7838240811/302231454903657293676544), (73803446907/1208925819614629174706176)), (11/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-70050602255/4835703278458516698824704), (-8820312295/1208925819614629174706176)), (123/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((73007704111/19342813113834066795298816), (-10006831947/9671406556917033397649408)), (339/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-37512809243/77371252455336267181195264), (62365154507/77371252455336267181195264)), (473/77371252455336267181195264), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((50256991607/137438953472), (23002094069/274877906944)), (271/68719476736), by norm_num⟩
  | 1 => ⟨((14115723033/274877906944), (7071030337/34359738368)), (1423/137438953472), by norm_num⟩
  | 2 => ⟨((-1719199953/68719476736), (21583111679/1099511627776)), (7359/549755813888), by norm_num⟩
  | 3 => ⟨((11198220441/2199023255552), (8266632265/2199023255552)), (50187/4398046511104), by norm_num⟩
  | 4 => ⟨((-1544047049/1099511627776), (45590852809/17592186044416)), (131441/17592186044416), by norm_num⟩
  | 5 => ⟨((-29331988419/140737488355328), (-52970507565/140737488355328)), (574133/140737488355328), by norm_num⟩
  | 6 => ⟨((55999140831/562949953421312), (46739024385/562949953421312)), (135655/70368744177664), by norm_num⟩
  | 7 => ⟨((-19280413625/562949953421312), (19653045589/2251799813685248)), (1815911/2251799813685248), by norm_num⟩
  | 8 => ⟨((39222580513/9007199254740992), (-62814430579/9007199254740992)), (685717/2251799813685248), by norm_num⟩
  | 9 => ⟨((15995695015/36028797018963968), (18697865039/9007199254740992)), (3807533/36028797018963968), by norm_num⟩
  | 10 => ⟨((-65143656883/144115188075855872), (-40128959569/144115188075855872)), (4934991/144115188075855872), by norm_num⟩
  | 11 => ⟨((74096928837/576460752303423488), (-9208890575/288230376151711744)), (6052081/576460752303423488), by norm_num⟩
  | 12 => ⟨((-2400071597/144115188075855872), (66301587519/2305843009213693952)), (3552837/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((50256991607/137438953472), (23002094069/274877906944)), (1085/274877906944), by norm_num⟩
  | 1 => ⟨((14115723033/274877906944), (7071030337/34359738368)), (2847/274877906944), by norm_num⟩
  | 2 => ⟨((-1719199953/68719476736), (21583111679/1099511627776)), (29437/2199023255552), by norm_num⟩
  | 3 => ⟨((11198220441/2199023255552), (8266632265/2199023255552)), (100375/8796093022208), by norm_num⟩
  | 4 => ⟨((-1544047049/1099511627776), (45590852809/17592186044416)), (65721/8796093022208), by norm_num⟩
  | 5 => ⟨((-29331988419/140737488355328), (-52970507565/140737488355328)), (574139/140737488355328), by norm_num⟩
  | 6 => ⟨((55999140831/562949953421312), (46739024385/562949953421312)), (1085263/562949953421312), by norm_num⟩
  | 7 => ⟨((-19280413625/562949953421312), (19653045589/2251799813685248)), (908001/1125899906842624), by norm_num⟩
  | 8 => ⟨((39222580513/9007199254740992), (-62814430579/9007199254740992)), (2743229/9007199254740992), by norm_num⟩
  | 9 => ⟨((15995695015/36028797018963968), (18697865039/9007199254740992)), (3808975/36028797018963968), by norm_num⟩
  | 10 => ⟨((-65143656883/144115188075855872), (-40128959569/144115188075855872)), (1235189/36028797018963968), by norm_num⟩
  | 11 => ⟨((74096928837/576460752303423488), (-9208890575/288230376151711744)), (1518785/144115188075855872), by norm_num⟩
  | 12 => ⟨((-2400071597/144115188075855872), (66301587519/2305843009213693952)), (1799477/576460752303423488), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile006Gamma
