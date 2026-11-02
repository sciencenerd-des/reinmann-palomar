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
namespace Reinmann.XiRectangle.Tile012Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨12,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (705/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (705/128))
  have he : value ((3/4), (705/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((876544/12220801), (-180480/12220801)), 0, by norm_num⟩
  | 1 => ⟨((-367878176768/149347977081601), (158198661120/149347977081601)), 0, by norm_num⟩
  | 2 => ⟨((11331691025/140737488355328), (-7906195353/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-11136180865/4503599627370496), (11750812989/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((10003358427/144115188075855872), (-4029183535/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-3835843907/2305843009213693952), (10429714215/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((484397427/18446744073709551616), (-25751232575/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1637623837/4722366482869645213696), (30468026817/4722366482869645213696)), (15/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-2269677357/37778931862957161709568), (-17289215493/75557863725914323419136)), (11/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((9294712189/2417851639229258349412352), (9384324557/1208925819614629174706176)), (1/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-3775395735/19342813113834066795298816), (-4835701723/19342813113834066795298816)), (3/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((10950635203/1237940039285380274899124224), (9314798685/1237940039285380274899124224)), (9/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-14768064319/39614081257132168796771975168), (-4051099601/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (705/256)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (705/256)))⁻¹=value ((876544/12220801), (-180480/12220801)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((876544/12220801), (-180480/12220801))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5613839191/2147483648), (1744286707/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((438272/12220801), (-90240/12220801)), 0, by norm_num⟩
  | 2 => ⟨((-91969544192/149347977081601), (39549665280/149347977081601)), 0, by norm_num⟩
  | 3 => ⟨((15108921367/1125899906842624), (-2635398451/281474976710656)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-11136180865/36028797018963968), (11750812989/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((4001343371/576460752303423488), (-805836707/72057594037927936)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-5114458543/36893488147419103232), (3476571405/9223372036854775808)), (5/36893488147419103232), by norm_num⟩
  | 7 => ⟨((4428776475/2361183241434822606848), (-14714990043/1180591620717411303424)), (13/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((1637623837/75557863725914323419136), (30468026817/75557863725914323419136)), (15/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-252186373/75557863725914323419136), (-15368191549/1208925819614629174706176)), (11/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((7435769751/38685626227668133590597632), (15014919291/38685626227668133590597632)), (7/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-10982969411/1237940039285380274899124224), (-14067495921/1237940039285380274899124224)), (9/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((14600846937/39614081257132168796771975168), (3104932895/9903520314283042199192993792)), (25/39614081257132168796771975168), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (15/4096)), 0, by norm_num⟩
  | 45 => ⟨((20999920501/816127672320), (-29805/6029312)), 0, by norm_num⟩
  | 44 => ⟨((-9996451453907/383035920875520), (24845480821/4741643894784)), 0, by norm_num⟩
  | 43 => ⟨((14643092903/549755813888), (-2942083369/549755813888)), (1/549755813888), by norm_num⟩
  | 42 => ⟨((-3746354427/137438953472), (3003042119/549755813888)), (1/274877906944), by norm_num⟩
  | 41 => ⟨((15350342451/549755813888), (-3071963815/549755813888)), (1/274877906944), by norm_num⟩
  | 40 => ⟨((-7866783567/274877906944), (1573040907/274877906944)), (1/274877906944), by norm_num⟩
  | 39 => ⟨((4034022595/137438953472), (-1612101051/274877906944)), (1/274877906944), by norm_num⟩
  | 38 => ⟨((-16559638693/549755813888), (3306300667/549755813888)), (1/274877906944), by norm_num⟩
  | 37 => ⟨((8503001667/274877906944), (-1696335367/274877906944)), (1/549755813888), by norm_num⟩
  | 36 => ⟨((-17477098681/549755813888), (1741834361/274877906944)), (1/549755813888), by norm_num⟩
  | 35 => ⟨((4493759851/137438953472), (-3579682605/549755813888)), (1/549755813888), by norm_num⟩
  | 34 => ⟨((-4625546663/137438953472), (920285003/137438953472)), (1/549755813888), by norm_num⟩
  | 33 => ⟨((9530593715/274877906944), (-3788517499/549755813888)), (1/274877906944), by norm_num⟩
  | 32 => ⟨((-19655018871/549755813888), (975587213/137438953472)), (1/274877906944), by norm_num⟩
  | 31 => ⟨((20287041115/549755813888), (-2011617033/274877906944)), (1/274877906944), by norm_num⟩
  | 30 => ⟨((-20961060889/549755813888), (4151849921/549755813888)), (1/274877906944), by norm_num⟩
  | 29 => ⟨((10840704121/274877906944), (-536120333/68719476736)), (1/274877906944), by norm_num⟩
  | 28 => ⟨((-11226514841/274877906944), (4435443291/549755813888)), (1/549755813888), by norm_num⟩
  | 27 => ⟨((23281601935/549755813888), (-574035761/68719476736)), (1/549755813888), by norm_num⟩
  | 26 => ⟨((-24173671863/549755813888), (2380315627/274877906944)), (1/549755813888), by norm_num⟩
  | 25 => ⟨((25136829835/549755813888), (-1235448173/137438953472)), (1/549755813888), by norm_num⟩
  | 24 => ⟨((-26179926279/549755813888), (5137292413/549755813888)), (1/549755813888), by norm_num⟩
  | 23 => ⟨((27313344491/549755813888), (-5348903449/549755813888)), (1/549755813888), by norm_num⟩
  | 22 => ⟨((-28549347547/549755813888), (5578703853/549755813888)), (1/549755813888), by norm_num⟩
  | 21 => ⟨((7475630975/137438953472), (-2914572633/274877906944)), (1/274877906944), by norm_num⟩
  | 20 => ⟨((-980948939/17179869184), (3051570431/274877906944)), (1/274877906944), by norm_num⟩
  | 19 => ⟨((16517015545/274877906944), (-400261211/34359738368)), (1/274877906944), by norm_num⟩
  | 18 => ⟨((-544677399/8589934592), (3368237361/274877906944)), (1/274877906944), by norm_num⟩
  | 17 => ⟨((18449106869/274877906944), (-3552582429/274877906944)), (1/137438953472), by norm_num⟩
  | 16 => ⟨((-19595208345/274877906944), (1879144987/137438953472)), (1/137438953472), by norm_num⟩
  | 15 => ⟨((20893159025/274877906944), (-1994652435/137438953472)), (1/137438953472), by norm_num⟩
  | 14 => ⟨((-22375284387/274877906944), (4250607907/274877906944)), (1/137438953472), by norm_num⟩
  | 13 => ⟨((24083788495/274877906944), (-284286255/17179869184)), (1/137438953472), by norm_num⟩
  | 12 => ⟨((-26074841101/274877906944), (2445766199/137438953472)), (1/274877906944), by norm_num⟩
  | 11 => ⟨((28424877897/274877906944), (-1322624069/68719476736)), (1/274877906944), by norm_num⟩
  | 10 => ⟨((-976270361/8589934592), (2880218801/137438953472)), (1/137438953472), by norm_num⟩
  | 9 => ⟨((17337963743/137438953472), (-1580546473/68719476736)), (1/137438953472), by norm_num⟩
  | 8 => ⟨((-19480294259/137438953472), (3502812231/137438953472)), (1/137438953472), by norm_num⟩
  | 7 => ⟨((5556805239/34359738368), (-3927611639/137438953472)), (1/137438953472), by norm_num⟩
  | 6 => ⟨((-25877128543/137438953472), (2235051977/68719476736)), (1/137438953472), by norm_num⟩
  | 5 => ⟨((7740966661/34359738368), (-1296831389/34359738368)), (1/68719476736), by norm_num⟩
  | 4 => ⟨((-19273454861/68719476736), (1545129929/34359738368)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((12768325281/34359738368), (-1912163123/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-18945552677/34359738368), (2511387437/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((4629466907/4294967296), (-1836458373/17179869184)), (1/17179869184), by norm_num⟩
  | 0 => ⟨((-10887992083/68719476736), (13954293657/68719476736)), (1/34359738368), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (705/4096)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (705/4096)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (705/4096))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((5613839191/2147483648), (1744286707/8589934592)), (1/8589934592), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (705/256))) (z:=((-21/128), (705/4096))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((5613839191/2147483648), (1744286707/8589934592))) (r:=(1/8589934592)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((17769319767/536870912), (2634301209/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((15368616175/8589934592), (225964489/2147483648)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((1384993496064/149347977081601), (-295476103200/149347977081601)), 0, by norm_num⟩
  | 3 => ⟨((-7694415803/70368744177664), (6870428621/140737488355328)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((2062617997/1125899906842624), (-12010445429/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 5 => ⟨((-4954640267/144115188075855872), (2753080951/72057594037927936)), (25/288230376151711744), by norm_num⟩
  | 6 => ⟨((1493607953/2305843009213693952), (-20667754491/18446744073709551616)), (9/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-6398692541/590295810358705651712), (9785822681/295147905179352825856)), (23/147573952589676412928), by norm_num⟩
  | 8 => ⟨((251210657/2361183241434822606848), (-18523493397/18889465931478580854784)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((434144577/151115727451828646838272), (17383393141/604462909807314587353088)), (147/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-5086928011/19342813113834066795298816), (-16048283061/19342813113834066795298816)), (99/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((4076787447/309485009821345068724781056), (3609203821/154742504910672534362390528)), (253/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-5486095671/9903520314283042199192993792), (-780203969/1237940039285380274899124224)), (85/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((10588671319/536870912), (1895055129/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((11073648879/8589934592), (225964489/2147483648)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((1384993496064/149347977081601), (-295476103200/149347977081601)), 0, by norm_num⟩
  | 3 => ⟨((-7694415803/70368744177664), (6870428621/140737488355328)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((2062617997/1125899906842624), (-12010445429/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 5 => ⟨((-4954640267/144115188075855872), (2753080951/72057594037927936)), (25/288230376151711744), by norm_num⟩
  | 6 => ⟨((1493607953/2305843009213693952), (-20667754491/18446744073709551616)), (9/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-6398692541/590295810358705651712), (9785822681/295147905179352825856)), (23/147573952589676412928), by norm_num⟩
  | 8 => ⟨((251210657/2361183241434822606848), (-18523493397/18889465931478580854784)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((434144577/151115727451828646838272), (17383393141/604462909807314587353088)), (147/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-5086928011/19342813113834066795298816), (-16048283061/19342813113834066795298816)), (99/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((4076787447/309485009821345068724781056), (3609203821/154742504910672534362390528)), (253/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-5486095671/9903520314283042199192993792), (-780203969/1237940039285380274899124224)), (85/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((22164045375/1073741824), (1895055129/268435456)), (5/1073741824), by norm_num⟩
  | 1 => ⟨((11073648879/8589934592), (225964489/2147483648)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((1384993496064/149347977081601), (-295476103200/149347977081601)), 0, by norm_num⟩
  | 3 => ⟨((-7694415803/70368744177664), (6870428621/140737488355328)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((2062617997/1125899906842624), (-12010445429/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 5 => ⟨((-4954640267/144115188075855872), (2753080951/72057594037927936)), (25/288230376151711744), by norm_num⟩
  | 6 => ⟨((1493607953/2305843009213693952), (-20667754491/18446744073709551616)), (9/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-6398692541/590295810358705651712), (9785822681/295147905179352825856)), (23/147573952589676412928), by norm_num⟩
  | 8 => ⟨((251210657/2361183241434822606848), (-18523493397/18889465931478580854784)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((434144577/151115727451828646838272), (17383393141/604462909807314587353088)), (147/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-5086928011/19342813113834066795298816), (-16048283061/19342813113834066795298816)), (99/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((4076787447/309485009821345068724781056), (3609203821/154742504910672534362390528)), (253/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-5486095671/9903520314283042199192993792), (-780203969/1237940039285380274899124224)), (85/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((735756353536/149347977081601), (-316397322240/149347977081601)), 0, by norm_num⟩
  | 1 => ⟨((-11331691025/35184372088832), (7906195353/35184372088832)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((16704271297/1125899906842624), (-4406554871/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-10003358427/18014398509481984), (4029183535/4503599627370496)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((4794804883/288230376151711744), (-13037142769/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-1453192281/4611686018427387904), (1207089027/576460752303423488)), (7/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-716460429/147573952589676412928), (-26659523465/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 7 => ⟨((2269677357/2361183241434822606848), (17289215493/4722366482869645213696)), (5/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-2614137803/37778931862957161709568), (-10557365127/75557863725914323419136)), (1/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((9438489337/2417851639229258349412352), (3022313577/604462909807314587353088)), (13/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-15057123403/77371252455336267181195264), (-50030657/302231454903657293676544)), (19/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((11076048239/1237940039285380274899124224), (3038324701/618970019642690137449562112)), (29/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-1915717923/4951760157141521099596496896), (-2359735669/19807040628566084398385987584)), (11/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11331691025/35184372088832), (-7906195353/35184372088832)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-16704271297/562949953421312), (4406554871/140737488355328)), (1/281474976710656), by norm_num⟩
  | 2 => ⟨((1875629705/1125899906842624), (-12087550605/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-4794804883/72057594037927936), (13037142769/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((1816490351/1152921504606846976), (-6035445135/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((268672661/9223372036854775808), (19994642599/36893488147419103232)), (9/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-3971935375/590295810358705651712), (-15128063557/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 7 => ⟨((10456551213/18889465931478580854784), (10557365127/9444732965739290427392)), (15/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-1327287563/37778931862957161709568), (-1700051387/37778931862957161709568)), (7/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((9410702127/4835703278458516698824704), (250153285/151115727451828646838272)), (11/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-15229566329/154742504910672534362390528), (-261106029/4835703278458516698824704)), (9/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((5747153769/1237940039285380274899124224), (7079207007/4951760157141521099596496896)), (29/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-16365246463/79228162514264337593543950336), (-785205391/39614081257132168796771975168)), (23/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11136180865/562949953421312), (-11750812989/562949953421312)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((-10003358427/4503599627370496), (4029183535/1125899906842624)), (3/4503599627370496), by norm_num⟩
  | 2 => ⟨((4794804883/36028797018963968), (-13037142769/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 3 => ⟨((-1210993567/288230376151711744), (2011815045/72057594037927936)), (5/576460752303423488), by norm_num⟩
  | 4 => ⟨((-895575537/9223372036854775808), (-8331101083/4611686018427387904)), (7/9223372036854775808), by norm_num⟩
  | 5 => ⟨((3971935375/147573952589676412928), (15128063557/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 6 => ⟨((-3049827437/1180591620717411303424), (-12316925981/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((7078867003/37778931862957161709568), (9066940731/37778931862957161709568)), (17/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-14116053191/1208925819614629174706176), (-750459855/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((6345652637/9671406556917033397649408), (435176715/1208925819614629174706176)), (15/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-21072897153/618970019642690137449562112), (-3244636545/309485009821345068724781056)), (13/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((16365246463/9903520314283042199192993792), (785205391/4951760157141521099596496896)), (11/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-23939979603/316912650057057350374175801344), (322619101/39614081257132168796771975168)), (9/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10003358427/9007199254740992), (-4029183535/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((-4794804883/36028797018963968), (13037142769/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((3632980701/576460752303423488), (-6035445135/144115188075855872)), (7/576460752303423488), by norm_num⟩
  | 3 => ⟨((895575537/4611686018427387904), (8331101083/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-1241229805/18446744073709551616), (-9455039723/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 5 => ⟨((1143685289/147573952589676412928), (4618847243/295147905179352825856)), (13/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-1548502157/2361183241434822606848), (-15867146279/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((14116053191/302231454903657293676544), (750459855/18889465931478580854784)), (1/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-14277718433/4835703278458516698824704), (-3916590435/2417851639229258349412352)), (17/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((13170560721/77371252455336267181195264), (4055795681/77371252455336267181195264)), (1/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-22502213887/2475880078570760549798248448), (-1079657413/1237940039285380274899124224)), (15/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((8977492351/19807040628566084398385987584), (-967857303/19807040628566084398385987584)), (27/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-13431941241/633825300114114700748351602688), (4309377899/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3835843907/72057594037927936), (-10429714215/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 1 => ⟨((-2906384561/576460752303423488), (1207089027/36028797018963968)), (7/576460752303423488), by norm_num⟩
  | 2 => ⟨((-268672661/1152921504606846976), (-19994642599/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((248245961/2305843009213693952), (15128063557/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-1143685289/73786976294838206464), (-4618847243/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 5 => ⟨((3716405177/2361183241434822606848), (9520287767/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-4940618617/37778931862957161709568), (-1050643797/9444732965739290427392)), (3/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((11422174747/1208925819614629174706176), (783318087/151115727451828646838272)), (7/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-23707009297/38685626227668133590597632), (-3650216113/19342813113834066795298816)), (15/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((22502213887/618970019642690137449562112), (1079657413/309485009821345068724781056)), (31/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-19750483173/9903520314283042199192993792), (2129286067/9903520314283042199192993792)), (15/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((16118329489/158456325028528675187087900672), (-5171253479/158456325028528675187087900672)), (29/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-12236895219/2535301200456458802993406410752), (3450721557/1267650600228229401496703205376)), (27/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((484397427/288230376151711744), (-25751232575/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 1 => ⟨((1432920859/9223372036854775808), (13329761733/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-248245961/2305843009213693952), (-3782015889/9223372036854775808)), (9/36893488147419103232), by norm_num⟩
  | 3 => ⟨((6099654875/295147905179352825856), (12316925981/295147905179352825856)), (9/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-1548502157/590295810358705651712), (-15867146279/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((4940618617/18889465931478580854784), (1050643797/4722366482869645213696)), (3/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-6662935269/302231454903657293676544), (-7310968811/604462909807314587353088)), (17/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((15804672865/9671406556917033397649408), (4866954817/9671406556917033397649408)), (21/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-16876660415/154742504910672534362390528), (-1619486119/154742504910672534362390528)), (3/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((16458735977/2475880078570760549798248448), (-27725079/38685626227668133590597632)), (27/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-14775135365/39614081257132168796771975168), (4740315689/39614081257132168796771975168)), (7/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((12236895219/633825300114114700748351602688), (-3450721557/316912650057057350374175801344)), (7/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-1163664063/1267650600228229401496703205376), (8108732057/10141204801825835211973625643008)), (7/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1637623837/36893488147419103232), (-30468026817/36893488147419103232)), (15/36893488147419103232), by norm_num⟩
  | 1 => ⟨((4539354715/73786976294838206464), (17289215493/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-5228275607/295147905179352825856), (-21114730253/590295810358705651712)), (17/590295810358705651712), by norm_num⟩
  | 3 => ⟨((14157734007/4722366482869645213696), (18133881461/4722366482869645213696)), (19/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((-1764506649/4722366482869645213696), (-750459855/2361183241434822606848)), (17/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((11422174747/302231454903657293676544), (783318087/37778931862957161709568)), (7/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-15804672865/4835703278458516698824704), (-76046169/75557863725914323419136)), (11/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((19287611903/77371252455336267181195264), (1850841279/77371252455336267181195264)), (29/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-21161231971/1237940039285380274899124224), (2281377929/1237940039285380274899124224)), (9/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((21107336235/19807040628566084398385987584), (-1692969889/4951760157141521099596496896)), (21/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-4807351693/79228162514264337593543950336), (5422562447/158456325028528675187087900672)), (47/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((15958821435/5070602400912917605986812821504), (-13900683525/5070602400912917605986812821504)), (25/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-185916331/1267650600228229401496703205376), (7807217869/40564819207303340847894502572032)), (51/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2269677357/147573952589676412928), (-17289215493/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 1 => ⟨((10456551213/1180591620717411303424), (21114730253/1180591620717411303424)), (1/73786976294838206464), by norm_num⟩
  | 2 => ⟨((-10618300505/4722366482869645213696), (-1700051387/590295810358705651712)), (15/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((14116053191/37778931862957161709568), (12007357679/37778931862957161709568)), (19/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((-7138859217/151115727451828646838272), (-7833180869/302231454903657293676544)), (9/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((11853504649/2417851639229258349412352), (3650216113/2417851639229258349412352)), (1/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-16876660415/38685626227668133590597632), (-809743059/19342813113834066795298816)), (27/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((21161231971/618970019642690137449562112), (-2281377929/618970019642690137449562112)), (37/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-23745753265/9903520314283042199192993792), (1904591125/2475880078570760549798248448)), (25/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((375574351/2475880078570760549798248448), (-6778203059/79228162514264337593543950336)), (31/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-1371461217/158456325028528675187087900672), (2389179981/316912650057057350374175801344)), (9/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((557748993/1267650600228229401496703205376), (-11710826803/20282409603651670423947251286016)), (41/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-6228390989/324518553658426726783156020576256), (12956767271/324518553658426726783156020576256)), (11/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9294712189/4722366482869645213696), (-9384324557/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 1 => ⟨((9438489337/9444732965739290427392), (12089254307/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((-9410702127/37778931862957161709568), (-250153285/1180591620717411303424)), (7/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((6345652637/151115727451828646838272), (6962827439/302231454903657293676544)), (9/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-13170560721/2417851639229258349412352), (-126743615/75557863725914323419136)), (19/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((22502213887/38685626227668133590597632), (2159314825/38685626227668133590597632)), (35/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-16458735977/309485009821345068724781056), (27725079/4835703278458516698824704)), (31/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((5276834059/1237940039285380274899124224), (-1692969889/1237940039285380274899124224)), (23/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((-12018379233/39614081257132168796771975168), (6778203059/39614081257132168796771975168)), (33/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((12190766373/633825300114114700748351602688), (-10618577693/633825300114114700748351602688)), (43/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-5453545709/5070602400912917605986812821504), (1789154095/1267650600228229401496703205376)), (13/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((4152260659/81129638414606681695789005144064), (-17275689695/162259276829213363391578010288128)), (31/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-4767205195/2596148429267413814265248164610048), (4766132559/649037107316853453566312041152512)), (35/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3775395735/18889465931478580854784), (-4835701723/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((15057123403/151115727451828646838272), (12807848191/151115727451828646838272)), (11/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((-1903695791/75557863725914323419136), (-261106029/18889465931478580854784)), (3/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((164632009/37778931862957161709568), (6489273089/4835703278458516698824704)), (17/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((-22502213887/38685626227668133590597632), (-269914353/4835703278458516698824704)), (19/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((19750483173/309485009821345068724781056), (-532321517/77371252455336267181195264)), (19/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((-14775135365/2475880078570760549798248448), (4740315689/2475880078570760549798248448)), (17/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((4807351693/9903520314283042199192993792), (-5422562447/19807040628566084398385987584)), (27/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((-1371461217/39614081257132168796771975168), (2389179981/79228162514264337593543950336)), (41/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((5453545709/2535301200456458802993406410752), (-1789154095/633825300114114700748351602688)), (7/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-9134973449/81129638414606681695789005144064), (2375407333/10141204801825835211973625643008)), (9/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((2860323117/649037107316853453566312041152512), (-5719359071/324518553658426726783156020576256)), (45/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-1062697691/20769187434139310514121985316880384), (25305592671/20769187434139310514121985316880384)), (53/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((219136/36662403), (-15040/12220801)), 0, by norm_num⟩
  | 1 => ⟨((-91969544192/448043931244803), (13183221760/149347977081601)), 0, by norm_num⟩
  | 2 => ⟨((15108921367/2251799813685248), (-2635398451/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-14848241153/72057594037927936), (3916937663/18014398509481984)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((3334452809/576460752303423488), (-10744489427/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-5114458543/36893488147419103232), (3476571405/9223372036854775808)), (5/36893488147419103232), by norm_num⟩
  | 6 => ⟨((161465809/73786976294838206464), (-17167488383/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((1091749225/37778931862957161709568), (10156008939/18889465931478580854784)), (11/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-756559119/151115727451828646838272), (-5763071831/302231454903657293676544)), (15/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((6196474793/19342813113834066795298816), (12512432743/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-1258465245/77371252455336267181195264), (-12895204595/618970019642690137449562112)), (17/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((14600846937/19807040628566084398385987584), (3104932895/4951760157141521099596496896)), (25/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-19690752425/633825300114114700748351602688), (-10802932269/633825300114114700748351602688)), (9/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22170463271/1073741824), (3789449537/536870912)), (3/536870912), by norm_num⟩
  | 1 => ⟨((22143771263/17179869184), (1809232411/17179869184)), (3/17179869184), by norm_num⟩
  | 2 => ⟨((20407618279/2199023255552), (-4360931441/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-15417832077/140737488355328), (107828589/2199023255552)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((16553044801/9007199254740992), (-12094386753/9007199254740992)), (9/4503599627370496), by norm_num⟩
  | 5 => ⟨((-9949237241/288230376151711744), (2780241665/72057594037927936)), (13/144115188075855872), by norm_num⟩
  | 6 => ⟨((2997307519/4611686018427387904), (-20935996497/18446744073709551616)), (73/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-6381633959/590295810358705651712), (19889020641/590295810358705651712)), (93/590295810358705651712), by norm_num⟩
  | 8 => ⟨((957557683/9444732965739290427392), (-9441842693/9444732965739290427392)), (113/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1930218145/604462909807314587353088), (2221800833/75557863725914323419136)), (37/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-2700772161/9671406556917033397649408), (-16451258205/19342813113834066795298816)), (25/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((8609851361/618970019642690137449562112), (1853116487/77371252455336267181195264)), (255/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-11587527355/19807040628566084398385987584), (-12820855137/19807040628566084398385987584)), (171/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-16116182791/18014398509481984), (2811091681/4503599627370496)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((5939296461/72057594037927936), (-6267100261/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 2 => ⟨((-2667562247/576460752303423488), (17191183083/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((852409757/4611686018427387904), (-1158857135/2305843009213693952)), (5/36893488147419103232), by norm_num⟩
  | 4 => ⟨((-161465809/36893488147419103232), (134121003/4611686018427387904)), (7/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-382112229/4722366482869645213696), (-14218412515/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1412243689/75557863725914323419136), (10757734085/151115727451828646838272)), (7/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-7435769751/4835703278458516698824704), (-3753729823/1208925819614629174706176)), (3/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((3775395735/38685626227668133590597632), (4835701723/38685626227668133590597632)), (11/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-3346027423/618970019642690137449562112), (-2846188487/618970019642690137449562112)), (17/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((5414956917/19807040628566084398385987584), (5941612749/39614081257132168796771975168)), (27/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-8173729805/633825300114114700748351602688), (-5034102761/1267650600228229401496703205376)), (11/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((2909377149/5070602400912917605986812821504), (279184139/5070602400912917605986812821504)), (17/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11085231155/536870912), (236840617/33554432)), (7/1073741824), by norm_num⟩
  | 1 => ⟨((22143772679/17179869184), (1809230917/17179869184)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((20407608103/2199023255552), (-2180457523/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-963612879/8796093022208), (6900958965/140737488355328)), (7/140737488355328), by norm_num⟩
  | 4 => ⟨((16553005381/9007199254740992), (-6047062399/4503599627370496)), (19/9007199254740992), by norm_num⟩
  | 5 => ⟨((-9949260563/288230376151711744), (2780133187/72057594037927936)), (27/288230376151711744), by norm_num⟩
  | 6 => ⟨((5994787431/9223372036854775808), (-20934683297/18446744073709551616)), (37/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-3191270823/295147905179352825856), (19887187765/590295810358705651712)), (47/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1916958821/18889465931478580854784), (-4720331051/4722366482869645213696)), (57/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((481737635/151115727451828646838272), (17771627183/604462909807314587353088)), (149/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-2698128139/9671406556917033397649408), (-16448357027/19342813113834066795298816)), (201/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((8601869203/618970019642690137449562112), (7411236919/309485009821345068724781056)), (1/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-11576162601/19807040628566084398385987584), (-6409882287/9903520314283042199192993792)), (343/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8129713515/9223372036854775808), (-13098044253/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-7793460635/73786976294838206464), (21190530469/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 2 => ⟨((2952517649/590295810358705651712), (-19619986725/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 3 => ⟨((1455665635/9444732965739290427392), (27082690505/9444732965739290427392)), (11/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-4034981969/75557863725914323419136), (-7684095775/37778931862957161709568)), (9/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((929471219/151115727451828646838272), (3753729823/302231454903657293676544)), (3/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-1258465245/2417851639229258349412352), (-12895204595/19342813113834066795298816)), (7/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((5736047011/154742504910672534362390528), (9758360527/309485009821345068724781056)), (7/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((-11603479107/4951760157141521099596496896), (-6366013659/4951760157141521099596496896)), (15/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((21407387585/158456325028528675187087900672), (412017339/9903520314283042199192993792)), (27/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-4571878377/633825300114114700748351602688), (-438717933/633825300114114700748351602688)), (25/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((29183975135/81129638414606681695789005144064), (-3146304375/81129638414606681695789005144064)), (45/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-5458058663/324518553658426726783156020576256), (1751112289/324518553658426726783156020576256)), (5/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22170462311/1073741824), (3789449871/536870912)), (1/134217728), by norm_num⟩
  | 1 => ⟨((22143772677/17179869184), (904615461/8589934592)), (5/17179869184), by norm_num⟩
  | 2 => ⟨((10203804057/1099511627776), (-4360915119/2199023255552)), (3/2199023255552), by norm_num⟩
  | 3 => ⟨((-7708903021/70368744177664), (6900959369/140737488355328)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((4138251225/2251799813685248), (-6047063315/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((-4974629395/144115188075855872), (1390067041/36028797018963968)), (7/72057594037927936), by norm_num⟩
  | 6 => ⟨((11989565261/18446744073709551616), (-20934695595/18446744073709551616)), (75/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-6382519765/590295810358705651712), (9943603189/295147905179352825856)), (95/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1916914557/18889465931478580854784), (-2360168561/2361183241434822606848)), (115/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1927032203/604462909807314587353088), (17771652331/604462909807314587353088)), (75/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5396395801/19342813113834066795298816), (-1028023151/1208925819614629174706176)), (101/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((8602091859/618970019642690137449562112), (7411224917/309485009821345068724781056)), (257/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-5788247867/9903520314283042199192993792), (-12819657695/19807040628566084398385987584)), (43/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-295251765/295147905179352825856), (15695989379/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((-1746798761/18889465931478580854784), (-16249614303/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((4841978363/75557863725914323419136), (18441829859/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-929471219/75557863725914323419136), (-15014919291/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((3775395735/2417851639229258349412352), (4835701723/2417851639229258349412352)), (5/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-12045698723/77371252455336267181195264), (-5123139277/38685626227668133590597632)), (1/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((16244870751/1237940039285380274899124224), (4456209561/618970019642690137449562112)), (21/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-9633324413/9903520314283042199192993792), (-2966524841/9903520314283042199192993792)), (27/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((2571681587/39614081257132168796771975168), (1974230697/316912650057057350374175801344)), (31/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((-20063982905/5070602400912917605986812821504), (2163084259/5070602400912917605986812821504)), (17/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((4502898397/20282409603651670423947251286016), (-2889335277/40564819207303340847894502572032)), (35/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((-14917357981/1298074214633706907132624082305024), (2103296949/324518553658426726783156020576256)), (35/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((11348495243/20769187434139310514121985316880384), (-2471232627/5192296858534827628530496329220096)), (35/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22170462311/1073741824), (3789449871/536870912)), (9/1073741824), by norm_num⟩
  | 1 => ⟨((22143772677/17179869184), (904615461/8589934592)), (3/8589934592), by norm_num⟩
  | 2 => ⟨((10203804057/1099511627776), (-2180457559/1099511627776)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-3854451511/35184372088832), (3450479683/70368744177664)), (9/140737488355328), by norm_num⟩
  | 4 => ⟨((8276502457/4503599627370496), (-3023531653/2251799813685248)), (21/9007199254740992), by norm_num⟩
  | 5 => ⟨((-9949258835/288230376151711744), (5560268145/144115188075855872)), (29/288230376151711744), by norm_num⟩
  | 6 => ⟨((11989565503/18446744073709551616), (-10467347731/9223372036854775808)), (19/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-6382520339/590295810358705651712), (19887206201/590295810358705651712)), (3/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1916915783/18889465931478580854784), (-9440674185/9444732965739290427392)), (29/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1927029811/604462909807314587353088), (17771652589/604462909807314587353088)), (151/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-5396391507/19342813113834066795298816), (-8224185897/9671406556917033397649408)), (203/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((4301042373/309485009821345068724781056), (7411226923/309485009821345068724781056)), (129/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-11576484911/19807040628566084398385987584), (-6409833561/9903520314283042199192993792)), (345/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3912709787/302231454903657293676544), (-14902488775/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((2253263561/302231454903657293676544), (18199902171/1208925819614629174706176)), (15/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((-9152474509/4835703278458516698824704), (-2930728317/1208925819614629174706176)), (7/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((12167372447/38685626227668133590597632), (2587444079/9671406556917033397649408)), (17/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((-6153360133/154742504910672534362390528), (-1687958167/77371252455336267181195264)), (17/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((20434324513/4951760157141521099596496896), (6292628451/4951760157141521099596496896)), (29/4951760157141521099596496896), by norm_num⟩
  | 6 => ⟨((-14546885745/39614081257132168796771975168), (-2791841389/79228162514264337593543950336)), (3/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((4559996115/158456325028528675187087900672), (-1966440235/633825300114114700748351602688)), (33/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((-10233859993/5070602400912917605986812821504), (1641667771/2535301200456458802993406410752)), (11/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((10359276375/81129638414606681695789005144064), (-11684983051/162259276829213363391578010288128)), (27/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((-1182134921/162259276829213363391578010288128), (8237442089/1298074214633706907132624082305024)), (1/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((1923013363/5192296858534827628530496329220096), (-10094180679/20769187434139310514121985316880384)), (9/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((-10737158877/664613997892457936451903530140172288), (11168122631/332306998946228968225951765070086144)), (77/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22170462311/1073741824), (3789449871/536870912)), (5/536870912), by norm_num⟩
  | 1 => ⟨((22143772677/17179869184), (904615461/8589934592)), (7/17179869184), by norm_num⟩
  | 2 => ⟨((10203804057/1099511627776), (-2180457559/1099511627776)), (5/2199023255552), by norm_num⟩
  | 3 => ⟨((-3854451511/35184372088832), (3450479683/70368744177664)), (5/70368744177664), by norm_num⟩
  | 4 => ⟨((8276502457/4503599627370496), (-3023531653/2251799813685248)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((-4974629417/144115188075855872), (5560268145/144115188075855872)), (15/144115188075855872), by norm_num⟩
  | 6 => ⟨((1498695687/2305843009213693952), (-20934695463/18446744073709551616)), (77/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-3191260161/295147905179352825856), (19887206199/590295810358705651712)), (97/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1916915745/18889465931478580854784), (-9440674179/9444732965739290427392)), (117/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((15054921/4722366482869645213696), (17771652545/604462909807314587353088)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-168637239/604462909807314587353088), (-16448371671/19342813113834066795298816)), (51/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((8602084975/618970019642690137449562112), (14822453545/618970019642690137449562112)), (259/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-11576485231/19807040628566084398385987584), (-1602458307/2475880078570760549798248448)), (173/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7413169097/19342813113834066795298816), (296722823/604462909807314587353088)), (25/38685626227668133590597632), by norm_num⟩
  | 1 => ⟨((-7391344493/38685626227668133590597632), (-12574409555/77371252455336267181195264)), (11/38685626227668133590597632), by norm_num⟩
  | 2 => ⟨((14951988929/309485009821345068724781056), (8203105713/309485009821345068724781056)), (25/309485009821345068724781056), by norm_num⟩
  | 3 => ⟨((-10344408965/1237940039285380274899124224), (-3185499091/1237940039285380274899124224)), (17/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((11046041813/9903520314283042199192993792), (2119958681/19807040628566084398385987584)), (19/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((-19390506557/158456325028528675187087900672), (2090477235/158456325028528675187087900672)), (39/158456325028528675187087900672), by norm_num⟩
  | 6 => ⟨((3626460131/316912650057057350374175801344), (-4653917661/1267650600228229401496703205376)), (35/1267650600228229401496703205376), by norm_num⟩
  | 7 => ⟨((-1179932963/1267650600228229401496703205376), (10647459281/20282409603651670423947251286016)), (27/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((10771717325/162259276829213363391578010288128), (-9382537061/162259276829213363391578010288128)), (41/162259276829213363391578010288128), by norm_num⟩
  | 9 => ⟨((-5354148195/1298074214633706907132624082305024), (878272291/162259276829213363391578010288128)), (7/324518553658426726783156020576256), by norm_num⟩
  | 10 => ⟨((8968477429/41538374868278621028243970633760768), (-18656901125/41538374868278621028243970633760768)), (9/5192296858534827628530496329220096), by norm_num⟩
  | 11 => ⟨((-5616380487/664613997892457936451903530140172288), (11230233569/332306998946228968225951765070086144)), (89/664613997892457936451903530140172288), by norm_num⟩
  | 12 => ⟨((1043328731/10633823966279326983230456482242756608), (-24844367417/10633823966279326983230456482242756608)), (105/10633823966279326983230456482242756608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22170462311/1073741824), (3789449871/536870912)), (11/1073741824), by norm_num⟩
  | 1 => ⟨((22143772677/17179869184), (904615461/8589934592)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((10203804057/1099511627776), (-2180457559/1099511627776)), (3/1099511627776), by norm_num⟩
  | 3 => ⟨((-3854451511/35184372088832), (3450479683/70368744177664)), (11/140737488355328), by norm_num⟩
  | 4 => ⟨((8276502457/4503599627370496), (-3023531653/2251799813685248)), (23/9007199254740992), by norm_num⟩
  | 5 => ⟨((-4974629417/144115188075855872), (5560268145/144115188075855872)), (31/288230376151711744), by norm_num⟩
  | 6 => ⟨((1498695687/2305843009213693952), (-20934695463/18446744073709551616)), (39/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-6382520323/590295810358705651712), (19887206199/590295810358705651712)), (49/295147905179352825856), by norm_num⟩
  | 8 => ⟨((958457873/9444732965739290427392), (-18881348359/18889465931478580854784)), (59/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((963514943/302231454903657293676544), (4442913137/151115727451828646838272)), (153/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-1349097911/4835703278458516698824704), (-514011615/604462909807314587353088)), (205/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((4301042485/309485009821345068724781056), (7411226783/309485009821345068724781056)), (65/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-11576485229/19807040628566084398385987584), (-6409833251/9903520314283042199192993792)), (347/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((173640424686697/262144), (680558298881959/1048576)), (2286073/131072), by norm_num⟩
  | 1 => ⟨((12566773621/16), (14501067695/16)), 25, by norm_num⟩
  | 2 => ⟨((7454277285/16), (5041273581/8)), (145/8), by norm_num⟩
  | 3 => ⟨((11776056165/64), (18664320659/64)), (563/64), by norm_num⟩
  | 4 => ⟨((6950950621/128), (6478996823/64)), (207/64), by norm_num⟩
  | 5 => ⟨((6519824929/512), (7206423971/256)), (123/128), by norm_num⟩
  | 6 => ⟨((5038566631/2048), (13387663981/2048)), (123/512), by norm_num⟩
  | 7 => ⟨((3277580639/8192), (21375577053/16384)), (425/8192), by norm_num⟩
  | 8 => ⟨((3624367087/65536), (7489093851/32768)), (649/65536), by norm_num⟩
  | 9 => ⟨((1697026899/262144), (18721908439/524288)), (445/262144), by norm_num⟩
  | 10 => ⟨((2617022211/4194304), (5284182707/1048576)), (277/1048576), by norm_num⟩
  | 11 => ⟨((750388133/16777216), (21774116095/33554432)), (1267/33554432), by norm_num⟩
  | 12 => ⟨((332406255/268435456), (10319627411/134217728)), (671/134217728), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((402717974933001/2535301200456458802993406410752), (126225529785/1267650600228229401496703205376)), (6673/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((226806682804051/79228162514264337593543950336), (1239865752687/633825300114114700748351602688)), (8203/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((964965793164013/19807040628566084398385987584), (349656325941/9903520314283042199192993792)), (18509/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1932259957561657/2475880078570760549798248448), (1489248771165/2475880078570760549798248448)), (9855/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1813972710909785/154742504910672534362390528), (746419389741/77371252455336267181195264)), (1235/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((397427771368979/2417851639229258349412352), (1403362280113/9671406556917033397649408)), (18577/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((646988134598183/302231454903657293676544), (1231781714793/604462909807314587353088)), (4077/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1945065189195177/75557863725914323419136), (1004437115933/37778931862957161709568)), (26599/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1340576220795267/4722366482869645213696), (1513010614169/4722366482869645213696)), (20037/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((420189313856185/147573952589676412928), (2090772199565/590295810358705651712)), (27693/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1897812271653583/73786976294838206464), (2629137463295/73786976294838206464)), (2177/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1906564815619835/9223372036854775808), (1489744918469/4611686018427387904)), (9871/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1678162989524819/1152921504606846976), (375858868371/144115188075855872)), (39861/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1268632029801539/144115188075855872), (1331076893031/72057594037927936)), (35307/144115188075855872), by norm_num⟩
  | 4 => ⟨((100219636451379/2251799813685248), (2028184531623/18014398509481984)), (26915/18014398509481984), by norm_num⟩
  | 3 => ⟨((1630520106416887/9007199254740992), (5182905224413/9007199254740992)), (68837/9007199254740992), by norm_num⟩
  | 2 => ⟨((628697453497309/1125899906842624), (5355545661063/2251799813685248)), (71219/2251799813685248), by norm_num⟩
  | 1 => ⟨((1328699534150493/1125899906842624), (4239578319069/562949953421312)), (56493/562949953421312), by norm_num⟩
  | 0 => ⟨((97154113529465/70368744177664), (18829755181023/1125899906842624)), (251865/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((97154113529465/70368744177664), (18829755181023/1125899906842624)), (960788731101607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((33528866001637/17592186044416), (25997169538373/562949953421312)), (703897/1125899906842624), by norm_num⟩
  | 2 => ⟨((2043679783732451/562949953421312), (99095770323623/562949953421312)), (1374061/562949953421312), by norm_num⟩
  | 3 => ⟨((231304258343539/17592186044416), (44968478377379/35184372088832)), (2615069/140737488355328), by norm_num⟩
  | 4 => ⟨((1506240292768565/8796093022208), (73906395953693/2199023255552)), (4715691/8796093022208), by norm_num⟩
  | 5 => ⟨((484360403730501/17179869184), (395490898621489/34359738368)), (7546891/34359738368), by norm_num⟩
  | 6 => ⟨((173640424686697/262144), (680558298881959/1048576)), (2286073/131072), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((22170462311/1073741824), (3789449871/536870912)), (11/1073741824), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((90112/620929), (-180480/620929)), 0, by norm_num⟩
  | 1 => ⟨((12226428928/385552823041), (16263413760/385552823041)), 0, by norm_num⟩
  | 2 => ⟨((-2018484439482368/239400928858025089), (370548576092160/239400928858025089)), 0, by norm_num⟩
  | 3 => ⟨((3402821843/8796093022208), (-23532245643/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((731530805/4398046511104), (10786483775/70368744177664)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((-19335285381/562949953421312), (7346638659/562949953421312)), (5/562949953421312), by norm_num⟩
  | 6 => ⟨((670640107/1125899906842624), (-26744781503/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 7 => ⟨((3692183229/4503599627370496), (9322077909/18014398509481984)), (5/9007199254740992), by norm_num⟩
  | 8 => ⟨((-19411486219/144115188075855872), (5879673303/72057594037927936)), (19/144115188075855872), by norm_num⟩
  | 9 => ⟨((-1201808997/576460752303423488), (-29394943861/1152921504606846976)), (17/576460752303423488), by norm_num⟩
  | 10 => ⟨((17785589955/4611686018427387904), (7134574825/4611686018427387904)), (31/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-4654868989/9223372036854775808), (8268360693/18446744073709551616)), (7/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-2104442309/73786976294838206464), (-15623686631/147573952589676412928)), (25/73786976294838206464), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (705/256)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (705/256)))⁻¹=value ((90112/620929), (-180480/620929)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((90112/620929), (-180480/620929))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((155648/866689), (-180480/866689)), 0, by norm_num⟩
  | 1 => ⟨((4173365248/751149822721), (28091351040/751149822721)), 0, by norm_num⟩
  | 2 => ⟨((-2859751494909952/651013288704240769), (-1809576823357440/651013288704240769)), 0, by norm_num⟩
  | 3 => ⟨((12030651031/17592186044416), (-7310644891/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-1399387989/35184372088832), (3161728747/35184372088832)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((-6513374233/1125899906842624), (-6873776409/562949953421312)), (1/281474976710656), by norm_num⟩
  | 6 => ⟨((16130132055/9007199254740992), (4450248333/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 7 => ⟨((-7647042049/36028797018963968), (5119469569/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 8 => ⟨((2457951427/576460752303423488), (-10047310389/288230376151711744)), (5/144115188075855872), by norm_num⟩
  | 9 => ⟨((14972392331/4611686018427387904), (16482491913/4611686018427387904)), (1/144115188075855872), by norm_num⟩
  | 10 => ⟨((-24484829331/36893488147419103232), (78892467/4611686018427387904)), (25/18446744073709551616), by norm_num⟩
  | 11 => ⟨((8531564647/147573952589676412928), (-5212086037/73786976294838206464)), (39/147573952589676412928), by norm_num⟩
  | 12 => ⟨((1277121555/590295810358705651712), (29189509247/2361183241434822606848)), (61/1180591620717411303424), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (705/256)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (705/256)))⁻¹=value ((155648/866689), (-180480/866689)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((155648/866689), (-180480/866689))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18547277824/538152334081), (-44354764800/538152334081)), 0, by norm_num⟩
  | 1 => ⟨((28758226393/1099511627776), (5260353329/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-2220259181/549755813888), (9516156833/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-5225007345/17592186044416), (-19876923197/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((7251634429/35184372088832), (4463026281/70368744177664)), (3/70368744177664), by norm_num⟩
  | 5 => ⟨((-2009824783/70368744177664), (3555103767/140737488355328)), (5/562949953421312), by norm_num⟩
  | 6 => ⟨((-5382505599/4503599627370496), (-28969905669/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 7 => ⟨((4648063485/4503599627370496), (1690585781/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 8 => ⟨((-10012987037/72057594037927936), (2097875225/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 9 => ⟨((-3073358039/576460752303423488), (-16757783419/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 10 => ⟨((20846193621/4611686018427387904), (7055682357/4611686018427387904)), (19/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-5188091779/9223372036854775808), (9571382203/18446744073709551616)), (35/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-4528165007/147573952589676412928), (-17448030959/147573952589676412928)), (61/147573952589676412928), by norm_num⟩
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
  | 0 => ⟨((27/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((24576/138169), (-60160/414507)), 0, by norm_num⟩
  | 1 => ⟨((-908296192/171816053049), (492830720/19090672561)), 0, by norm_num⟩
  | 2 => ⟨((-3701322285056/2637739137080809), (-190830954414080/71218956701181843)), 0, by norm_num⟩
  | 3 => ⟨((5616140583/17592186044416), (9603291201/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-21558152217/562949953421312), (6209174911/562949953421312)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((5866706637/2251799813685248), (-4233290355/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((1482415469/36028797018963968), (18859322209/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((-12003390551/288230376151711744), (-12557356023/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 8 => ⟨((989390117/144115188075855872), (1965754685/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 9 => ⟨((-3101013673/4611686018427387904), (7791580741/18446744073709551616)), (17/18446744073709551616), by norm_num⟩
  | 10 => ⟨((8603659711/295147905179352825856), (-6372319865/73786976294838206464)), (45/295147905179352825856), by norm_num⟩
  | 11 => ⟨((8676373901/2361183241434822606848), (1445614769/147573952589676412928)), (59/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-19600949051/18889465931478580854784), (-11419309369/18889465931478580854784)), (77/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (705/256)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (705/256)))⁻¹=value ((24576/138169), (-60160/414507)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((24576/138169), (-60160/414507))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1345278783258624/74355969847637689), (-2154383865282560/223067909542913067)), 0, by norm_num⟩
  | 1 => ⟨((16836865457/2199023255552), (-7474781823/2199023255552)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-1153471115/2199023255552), (9736354997/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-11639517793/35184372088832), (-13820777951/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((29214551617/281474976710656), (-2168568699/281474976710656)), (7/281474976710656), by norm_num⟩
  | 5 => ⟨((-1419404311/140737488355328), (4744386575/281474976710656)), (7/1125899906842624), by norm_num⟩
  | 6 => ⟨((-6631134847/4503599627370496), (-901175455/281474976710656)), (7/4503599627370496), by norm_num⟩
  | 7 => ⟨((21665563055/36028797018963968), (854443397/9007199254740992)), (15/36028797018963968), by norm_num⟩
  | 8 => ⟨((-9825535907/144115188075855872), (10964758331/144115188075855872)), (15/144115188075855872), by norm_num⟩
  | 9 => ⟨((-5332533789/1152921504606846976), (-9287304005/576460752303423488)), (27/1152921504606846976), by norm_num⟩
  | 10 => ⟨((12020614735/4611686018427387904), (3289259949/4611686018427387904)), (25/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-1421855621/4611686018427387904), (5527552779/18446744073709551616)), (23/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-5000577811/295147905179352825856), (-19361588641/295147905179352825856)), (5/18446744073709551616), by norm_num⟩
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
  | 0 => ⟨((35/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((57344/350285), (-36096/350285)), 0, by norm_num⟩
  | 1 => ⟨((-198541312/24539916245), (2069889024/122699581225)), 0, by norm_num⟩
  | 2 => ⟨((-8894474616832/42979822809399125), (-77264226091008/42979822809399125)), 0, by norm_num⟩
  | 3 => ⟨((3854895193/35184372088832), (4802104397/35184372088832)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-18014673549/1125899906842624), (-6222388177/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((14361297385/9007199254740992), (-3350883181/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-16045922787/144115188075855872), (16227664571/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((954604439/288230376151711744), (-17240279499/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((1151467465/2305843009213693952), (12863310675/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-2079543981/18446744073709551616), (-3262373261/36893488147419103232)), (31/147573952589676412928), by norm_num⟩
  | 10 => ⟨((16272800277/1180591620717411303424), (843909233/590295810358705651712)), (17/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-22703134977/18889465931478580854784), (5602258009/9444732965739290427392)), (73/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((10248230577/151115727451828646838272), (-16695024071/151115727451828646838272)), (79/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (705/256)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (705/256)))⁻¹=value ((57344/350285), (-36096/350285)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((57344/350285), (-36096/350285))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-17403417589/4398046511104), (1245980723/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((5332430179/4398046511104), (-13832030539/8796093022208)), (3/8796093022208), by norm_num⟩
  | 2 => ⟨((4364057387/35184372088832), (21379816261/35184372088832)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-19153780339/140737488355328), (-323535921/4398046511104)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((17523241105/562949953421312), (-7288731807/562949953421312)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((-4041850093/2251799813685248), (7275820851/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 6 => ⟨((-26634501/35184372088832), (-17903348461/18014398509481984)), (13/18014398509481984), by norm_num⟩
  | 7 => ⟨((31905329979/144115188075855872), (-589668443/144115188075855872)), (27/144115188075855872), by norm_num⟩
  | 8 => ⟨((-6119582051/288230376151711744), (17998601309/576460752303423488)), (27/576460752303423488), by norm_num⟩
  | 9 => ⟨((-2638116833/1152921504606846976), (-13397980747/2305843009213693952)), (25/2305843009213693952), by norm_num⟩
  | 10 => ⟨((2275594323/2305843009213693952), (1898831469/9223372036854775808)), (23/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-16378068235/147573952589676412928), (4236196283/36893488147419103232)), (85/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-3757420711/590295810358705651712), (-14232037295/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
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
  | 0 => ⟨((43/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((352256/2390401), (-180480/2390401)), 0, by norm_num⟩
  | 1 => ⟨((-45755629568/5714016940801), (63575162880/5714016940801)), 0, by norm_num⟩
  | 2 => ⟨((2321824826261504/13658791809307651201), (-15326354299944960/13658791809307651201)), 0, by norm_num⟩
  | 3 => ⟨((4198900419/140737488355328), (25077761137/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-97841979/17592186044416), (-6122953205/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((22161019781/36028797018963968), (6872163795/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((-7569140329/144115188075855872), (660500025/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((8125368109/2305843009213693952), (-12258419505/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 8 => ⟨((-5876871345/36893488147419103232), (3033396779/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-400624365/590295810358705651712), (-17854030695/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 10 => ⟨((5628206809/4722366482869645213696), (10403082581/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-201855147/1180591620717411303424), (-1108085837/9444732965739290427392)), (13/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((20584324057/1208925819614629174706176), (330934765/151115727451828646838272)), (47/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (705/256)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (705/256)))⁻¹=value ((352256/2390401), (-180480/2390401)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((352256/2390401), (-180480/2390401))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19764327961/35184372088832), (11980828295/35184372088832)), (3/35184372088832), by norm_num⟩
  | 1 => ⟨((6226006703/70368744177664), (-26006123047/70368744177664)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((10075303441/140737488355328), (487086901/4398046511104)), (3/70368744177664), by norm_num⟩
  | 3 => ⟨((-9870029849/281474976710656), (-3390490377/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((903606925/140737488355328), (-5785035033/1125899906842624)), (9/2251799813685248), by norm_num⟩
  | 5 => ⟨((-501690247/9007199254740992), (7695657195/4503599627370496)), (9/9007199254740992), by norm_num⟩
  | 6 => ⟨((-17797791579/72057594037927936), (-15658642221/72057594037927936)), (9/36028797018963968), by norm_num⟩
  | 7 => ⟨((8462124629/144115188075855872), (-1532078907/144115188075855872)), (19/288230376151711744), by norm_num⟩
  | 8 => ⟨((-10829280225/2305843009213693952), (21223043533/2305843009213693952)), (37/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-3584737885/4611686018427387904), (-14194222497/9223372036854775808)), (35/9223372036854775808), by norm_num⟩
  | 10 => ⟨((20390554339/73786976294838206464), (183882171/4611686018427387904)), (65/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-8722190093/295147905179352825856), (302473457/9223372036854775808)), (15/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-4294880051/2361183241434822606848), (-15593870635/2361183241434822606848)), (107/2361183241434822606848), by norm_num⟩
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
  | 0 => ⟨((51/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((139264/1053483), (-60160/1053483)), 0, by norm_num⟩
  | 1 => ⟨((-2629206016/369942143763), (8378122240/1109826431289)), 0, by norm_num⟩
  | 2 => ⟨((297216702939136/1169183278313629587), (-820644958699520/1169183278313629587)), 0, by norm_num⟩
  | 3 => ⟨((911624999/281474976710656), (30203148985/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-3931595537/2251799813685248), (-15554212533/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((15421612823/72057594037927936), (12857101855/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((-22182863783/1152921504606846976), (-102370803/18014398509481984)), (7/1152921504606846976), by norm_num⟩
  | 7 => ⟨((6613161299/4611686018427387904), (-3205373145/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-13255328969/147573952589676412928), (3868660853/73786976294838206464)), (9/147573952589676412928), by norm_num⟩
  | 9 => ⟨((10483418221/2361183241434822606848), (-3559565671/590295810358705651712)), (15/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-4582049237/37778931862957161709568), (1240437603/2361183241434822606848)), (3/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-1055320521/151115727451828646838272), (-23082509501/604462909807314587353088)), (37/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((7504692149/4835703278458516698824704), (11241226571/4835703278458516698824704)), (29/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (705/256)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (705/256)))⁻¹=value ((139264/1053483), (-60160/1053483)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((139264/1053483), (-60160/1053483))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7714192783/140737488355328), (5424900149/70368744177664)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((-2248060673/281474976710656), (-17048367709/281474976710656)), (3/140737488355328), by norm_num⟩
  | 2 => ⟨((10158697289/562949953421312), (2016446709/140737488355328)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((-29639136863/4503599627370496), (3488052375/4503599627370496)), (15/4503599627370496), by norm_num⟩
  | 4 => ⟨((8720934663/9007199254740992), (-5787056401/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((4533284533/72057594037927936), (6154616695/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((-16998093797/288230376151711744), (-10205544423/288230376151711744)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((13908883041/1152921504606846976), (-4729302329/1152921504606846976)), (21/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-7152815725/9223372036854775808), (19373736059/9223372036854775808)), (41/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-7354922349/36893488147419103232), (-5903497685/18446744073709551616)), (5/4611686018427387904), by norm_num⟩
  | 10 => ⟨((9020083911/147573952589676412928), (1461256393/295147905179352825856)), (73/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-14675258643/2361183241434822606848), (8784507131/1180591620717411303424)), (135/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-3959656765/9444732965739290427392), (-13585723537/9444732965739290427392)), (121/9444732965739290427392), by norm_num⟩
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
  | 0 => ⟨((59/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((483328/4061569), (-180480/4061569)), 0, by norm_num⟩
  | 1 => ⟨((-100516462592/16496342741761), (87231037440/16496342741761)), 0, by norm_num⟩
  | 2 => ⟨((4311195761/17592186044416), (-15833356869/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-1289983257/281474976710656), (18138554693/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-3991908143/9007199254740992), (-9092548933/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((10264895053/144115188075855872), (7946591477/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-481938929/72057594037927936), (-11481301087/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 7 => ⟨((18763294161/36893488147419103232), (5447871951/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-19799358071/590295810358705651712), (1483742417/590295810358705651712)), (9/295147905179352825856), by norm_num⟩
  | 9 => ⟨((9160793089/4722366482869645213696), (-8450965427/9444732965739290427392)), (25/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-14437977765/151115727451828646838272), (7279224449/75557863725914323419136)), (17/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((8569634169/2417851639229258349412352), (-4748052891/604462909807314587353088)), (23/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-21981339/604462909807314587353088), (5281759441/9671406556917033397649408)), (61/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (705/256)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (705/256)))⁻¹=value ((483328/4061569), (-180480/4061569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((483328/4061569), (-180480/4061569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-435869343/140737488355328), (26142684433/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 1 => ⟨((-8366543463/2251799813685248), (-4285342629/562949953421312)), (9/2251799813685248), by norm_num⟩
  | 2 => ⟨((14295713721/4503599627370496), (1433851181/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | 3 => ⟨((-8700196073/9007199254740992), (6833959151/18014398509481984)), (13/18014398509481984), by norm_num⟩
  | 4 => ⟨((3860923675/36028797018963968), (-4322917437/18014398509481984)), (9/36028797018963968), by norm_num⟩
  | 5 => ⟨((779072323/36028797018963968), (15714341627/288230376151711744)), (19/288230376151711744), by norm_num⟩
  | 6 => ⟨((-12785013275/1152921504606846976), (-5022662099/1152921504606846976)), (19/1152921504606846976), by norm_num⟩
  | 7 => ⟨((18538511819/9223372036854775808), (-4664209749/4611686018427387904)), (19/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-3544323467/36893488147419103232), (448781855/1152921504606846976)), (19/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-377019905/9223372036854775808), (-16091547291/295147905179352825856)), (73/295147905179352825856), by norm_num⟩
  | 10 => ⟨((26296705417/2361183241434822606848), (246615519/1180591620717411303424)), (17/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-2541279959/2361183241434822606848), (6595483527/4722366482869645213696)), (63/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-6105175051/75557863725914323419136), (-19611739225/75557863725914323419136)), (113/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((67/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((548864/5093761), (-180480/5093761)), 0, by norm_num⟩
  | 1 => ⟨((-134339330048/25946401125121), (99058974720/25946401125121)), 0, by norm_num⟩
  | 2 => ⟨((7434860889/35184372088832), (-10464346653/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-1721417399/281474976710656), (22255765371/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-11652705/562949953421312), (-21136624279/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((6312666745/288230376151711744), (4528611995/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-661013649/288230376151711744), (-6912816115/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((13035799099/73786976294838206464), (1115010287/9223372036854775808)), (5/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-13765510065/1180591620717411303424), (-3994236915/1180591620717411303424)), (3/295147905179352825856), by norm_num⟩
  | 9 => ⟨((12998289939/18889465931478580854784), (-458767353/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-11074716819/302231454903657293676544), (4079865157/302231454903657293676544)), (33/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((16780306131/9671406556917033397649408), (-13312147157/9671406556917033397649408)), (39/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-5345778591/77371252455336267181195264), (16231728167/154742504910672534362390528)), (23/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (705/256)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (705/256)))⁻¹=value ((548864/5093761), (-180480/5093761)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((548864/5093761), (-180480/5093761))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1398579681/18014398509481984), (3064028629/2251799813685248)), (11/18014398509481984), by norm_num⟩
  | 1 => ⟨((-6290239281/9007199254740992), (-13700491953/18014398509481984)), (3/4503599627370496), by norm_num⟩
  | 2 => ⟨((15789877903/36028797018963968), (480593621/9007199254740992)), (7/18014398509481984), by norm_num⟩
  | 3 => ⟨((-16601355753/144115188075855872), (11527821087/144115188075855872)), (19/144115188075855872), by norm_num⟩
  | 4 => ⟨((2257883565/288230376151711744), (-20755223819/576460752303423488)), (13/288230376151711744), by norm_num⟩
  | 5 => ⟨((5162238735/1152921504606846976), (8286121649/1152921504606846976)), (29/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-7921963123/4611686018427387904), (-886361071/2305843009213693952)), (15/4611686018427387904), by norm_num⟩
  | 7 => ⟨((645866083/2305843009213693952), (-7006718055/36893488147419103232)), (15/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-2445548079/295147905179352825856), (8934318641/147573952589676412928)), (59/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-8219762595/1180591620717411303424), (-9249792017/1180591620717411303424)), (57/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((32515491009/18889465931478580854784), (-1385125907/18889465931478580854784)), (211/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-745786005/4722366482869645213696), (16854827951/75557863725914323419136)), (197/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-63027305/4722366482869645213696), (-24130877683/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((75/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((8192/83427), (-12032/417135)), 0, by norm_num⟩
  | 1 => ⟨((-85164032/19333512025), (98566144/34800321645)), 0, by norm_num⟩
  | 2 => ⟨((2546512953344/14516432169387075), (-14704294494208/72582160846935375)), 0, by norm_num⟩
  | 3 => ⟨((-1601855403/281474976710656), (1755899951/140737488355328)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((1791881929/18014398509481984), (-6256654491/9007199254740992)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((92493617/18014398509481984), (20486607329/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((-3526226215/4611686018427387904), (-15410247019/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 7 => ⟨((4548019645/73786976294838206464), (10478115915/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-19126525849/4722366482869645213696), (-12264234193/4722366482869645213696)), (13/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((4463714455/18889465931478580854784), (81572115/1180591620717411303424)), (7/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-3807637433/302231454903657293676544), (38097753/2417851639229258349412352)), (15/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((23919896281/38685626227668133590597632), (-7058979615/38685626227668133590597632)), (31/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-17161356567/618970019642690137449562112), (1383101387/77371252455336267181195264)), (1/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (705/256)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (705/256)))⁻¹=value ((8192/83427), (-12032/417135)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((8192/83427), (-12032/417135))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1688743277/36028797018963968), (18932828757/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 1 => ⟨((-13648740853/144115188075855872), (-2172879927/36028797018963968)), (13/144115188075855872), by norm_num⟩
  | 2 => ⟨((1804780245/36028797018963968), (-836855957/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((-13120008833/1152921504606846976), (14048135131/1152921504606846976)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((262083677/2305843009213693952), (-5215508495/1152921504606846976)), (33/4611686018427387904), by norm_num⟩
  | 5 => ⟨((1629384619/2305843009213693952), (14763161009/18446744073709551616)), (37/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-16675901681/73786976294838206464), (-1276374019/73786976294838206464)), (39/73786976294838206464), by norm_num⟩
  | 7 => ⟨((2462370843/73786976294838206464), (-4300029345/147573952589676412928)), (5/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-168548177/590295810358705651712), (2389413287/295147905179352825856)), (39/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-9561798103/9444732965739290427392), (-1145288709/1180591620717411303424)), (19/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((4356049809/18889465931478580854784), (-1800093453/75557863725914323419136)), (71/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-3030094643/151115727451828646838272), (18711187597/604462909807314587353088)), (33/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-4652004445/2417851639229258349412352), (-3230258715/604462909807314587353088)), (15/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((83/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((679936/7551361), (-180480/7551361)), 0, by norm_num⟩
  | 1 => ⟨((-214869966848/57023052952321), (122714849280/57023052952321)), 0, by norm_num⟩
  | 2 => ⟨((1265993647/8796093022208), (-4993202697/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-10772120799/2251799813685248), (9130019137/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((2134068823/18014398509481984), (-15212950085/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-331441619/1152921504606846976), (1471806991/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((-4263865571/18446744073709551616), (-17026410487/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 7 => ⟨((790861709/36893488147419103232), (11449408373/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-13493243401/9444732965739290427392), (-7037658151/4722366482869645213696)), (15/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((6205427091/75557863725914323419136), (3779479591/75557863725914323419136)), (15/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-20770459793/4835703278458516698824704), (-6143946783/4835703278458516698824704)), (7/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((32272736775/154742504910672534362390528), (454316001/77371252455336267181195264)), (13/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-23420822239/2475880078570760549798248448), (2758057481/1237940039285380274899124224)), (3/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (705/256)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (705/256)))⁻¹=value ((679936/7551361), (-180480/7551361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((679936/7551361), (-180480/7551361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8485830651/1152921504606846976), (12346356433/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 1 => ⟨((-24046094997/2305843009213693952), (-4105541227/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 2 => ⟨((22522017575/4611686018427387904), (-7767887531/4611686018427387904)), (33/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-4303492667/4611686018427387904), (1733202401/1152921504606846976)), (13/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-681028647/9223372036854775808), (-9018098991/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 5 => ⟨((211953887/2305843009213693952), (11259837249/147573952589676412928)), (21/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-15237296667/590295810358705651712), (1779550819/1180591620717411303424)), (89/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((2037998105/590295810358705651712), (-2241682969/590295810358705651712)), (23/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((1090414205/18889465931478580854784), (8953565271/9444732965739290427392)), (91/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-9691865721/75557863725914323419136), (-7944313145/75557863725914323419136)), (11/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((16457195983/604462909807314587353088), (-2693500715/604462909807314587353088)), (83/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-338215359/151115727451828646838272), (9169577453/2417851639229258349412352)), (309/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-148410265/604462909807314587353088), (-12237873165/19342813113834066795298816)), (565/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((91/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((745472/8976769), (-180480/8976769)), 0, by norm_num⟩
  | 1 => ⟨((-261577736192/80582381679361), (134542786560/80582381679361)), 0, by norm_num⟩
  | 2 => ⟨((4151790235/35184372088832), (-14349393597/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-4362547337/1125899906842624), (6102120507/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((3833621971/36028797018963968), (-4755664335/18014398509481984)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((-2034145229/1152921504606846976), (3467760527/288230376151711744)), (9/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-1759291999/36893488147419103232), (-19084988879/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((4238461939/590295810358705651712), (12396271139/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-4809689289/9444732965739290427392), (-15107645841/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1102579927/37778931862957161709568), (2122416543/75557863725914323419136)), (3/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-7225543763/4835703278458516698824704), (-8442876351/9671406556917033397649408)), (21/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((21917287067/309485009821345068724781056), (3284741441/154742504910672534362390528)), (9/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-15617542655/4951760157141521099596496896), (-1678525667/9903520314283042199192993792)), (61/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (705/256)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (705/256)))⁻¹=value ((745472/8976769), (-180480/8976769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((745472/8976769), (-180480/8976769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((15246856959/18446744073709551616), (854688397/1152921504606846976)), (5/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-18066422261/18446744073709551616), (-2002016143/18446744073709551616)), (23/18446744073709551616), by norm_num⟩
  | 2 => ⟨((3813454957/9223372036854775808), (-8980103197/36893488147419103232)), (15/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-9148272275/147573952589676412928), (23297019597/147573952589676412928)), (49/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-1104859069/73786976294838206464), (-853933463/18446744073709551616)), (9/73786976294838206464), by norm_num⟩
  | 5 => ⟨((189164005/18446744073709551616), (1847569515/295147905179352825856)), (21/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-24575620395/9444732965739290427392), (4602571333/9444732965739290427392)), (45/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((11843881781/37778931862957161709568), (-16289212549/37778931862957161709568)), (47/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((2292496009/151115727451828646838272), (1862880773/18889465931478580854784)), (47/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-17393300417/1208925819614629174706176), (-6102051707/604462909807314587353088)), (181/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((27759581743/9671406556917033397649408), (-6217747995/9671406556917033397649408)), (343/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-2150275857/9671406556917033397649408), (16073438921/38685626227668133590597632)), (5/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-8682494605/309485009821345068724781056), (-20763863751/309485009821345068724781056)), (587/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((99/8), (705/256)), 0, by norm_num⟩
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
  | 0 => ⟨((90112/1170361), (-60160/3511083)), 0, by norm_num⟩
  | 1 => ⟨((-34731163648/12327703832889), (5421137920/4109234610963)), 0, by norm_num⟩
  | 2 => ⟨((6836872259/70368744177664), (-10544702441/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-6977074821/2251799813685248), (16738881533/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((3150364585/36028797018963968), (-12223246037/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-4411007951/2305843009213693952), (16785409209/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((832308561/73786976294838206464), (-10943783721/36893488147419103232)), (7/73786976294838206464), by norm_num⟩
  | 7 => ⟨((4975117205/2361183241434822606848), (27191925067/2361183241434822606848)), (3/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-6791795003/37778931862957161709568), (-4016796643/9444732965739290427392)), (5/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1596469601/151115727451828646838272), (17931536505/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-10324852781/19342813113834066795298816), (-9294433571/19342813113834066795298816)), (13/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((15267460325/618970019642690137449562112), (4309728595/309485009821345068724781056)), (5/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-10585658497/9903520314283042199192993792), (-6432928715/19807040628566084398385987584)), (31/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (705/256)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (705/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (705/256)))⁻¹=value ((90112/1170361), (-60160/3511083)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((90112/1170361), (-60160/3511083))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11265955687/147573952589676412928), (6333311437/147573952589676412928)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-23781190967/295147905179352825856), (1095983867/147573952589676412928)), (37/295147905179352825856), by norm_num⟩
  | 2 => ⟨((18123086615/590295810358705651712), (-15820840435/590295810358705651712)), (49/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-445731775/147573952589676412928), (17132688919/1180591620717411303424)), (21/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-9228083277/4722366482869645213696), (-2297566345/590295810358705651712)), (31/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((18991190575/18889465931478580854784), (4149719275/9444732965739290427392)), (75/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-17715578705/75557863725914323419136), (2788231777/37778931862957161709568)), (81/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((3799725905/151115727451828646838272), (-1640351569/37778931862957161709568)), (43/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((2734375027/1208925819614629174706176), (22293298117/2417851639229258349412352)), (43/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-6996274745/4835703278458516698824704), (-2094651597/2417851639229258349412352)), (167/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((21130182295/77371252455336267181195264), (-6013583797/77371252455336267181195264)), (317/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-3071220761/154742504910672534362390528), (12729728247/309485009821345068724781056)), (297/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-896872445/309485009821345068724781056), (-15941058743/2475880078570760549798248448)), (273/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1560846413/68719476736), (5358387151/68719476736)), (153/68719476736), by norm_num⟩
  | 1 => ⟨((-10205300107/274877906944), (7630748755/137438953472)), (669/137438953472), by norm_num⟩
  | 2 => ⟨((-26125907731/1099511627776), (3389188693/1099511627776)), (6383/1099511627776), by norm_num⟩
  | 3 => ⟨((-254425497/68719476736), (-1499317697/549755813888)), (20951/4398046511104), by norm_num⟩
  | 4 => ⟨((-10218472643/35184372088832), (-13999175713/35184372088832)), (52553/17592186044416), by norm_num⟩
  | 5 => ⟨((-10763624859/140737488355328), (-69122969/1099511627776)), (214489/140737488355328), by norm_num⟩
  | 6 => ⟨((-1313764277/281474976710656), (-21092762979/1125899906842624)), (742347/1125899906842624), by norm_num⟩
  | 7 => ⟨((2074241167/2251799813685248), (-5327319669/4503599627370496)), (560321/2251799813685248), by norm_num⟩
  | 8 => ⟨((-16335692511/144115188075855872), (-6982103769/144115188075855872)), (12055893/144115188075855872), by norm_num⟩
  | 9 => ⟨((-87336479/144115188075855872), (-6438160865/144115188075855872)), (14678219/576460752303423488), by norm_num⟩
  | 10 => ⟨((24108998679/4611686018427387904), (258184409/2305843009213693952)), (16394997/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-17828214971/36893488147419103232), (15292470335/36893488147419103232)), (33972563/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-3504011585/147573952589676412928), (-583322131/4611686018427387904)), (65923749/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1560846413/68719476736), (5358387151/68719476736)), (613/274877906944), by norm_num⟩
  | 1 => ⟨((-10205300107/274877906944), (7630748755/137438953472)), (1339/274877906944), by norm_num⟩
  | 2 => ⟨((-26125907731/1099511627776), (3389188693/1099511627776)), (399/68719476736), by norm_num⟩
  | 3 => ⟨((-254425497/68719476736), (-1499317697/549755813888)), (2619/549755813888), by norm_num⟩
  | 4 => ⟨((-10218472643/35184372088832), (-13999175713/35184372088832)), (26277/8796093022208), by norm_num⟩
  | 5 => ⟨((-10763624859/140737488355328), (-69122969/1099511627776)), (214495/140737488355328), by norm_num⟩
  | 6 => ⟨((-1313764277/281474976710656), (-21092762979/1125899906842624)), (742393/1125899906842624), by norm_num⟩
  | 7 => ⟨((2074241167/2251799813685248), (-5327319669/4503599627370496)), (2241645/9007199254740992), by norm_num⟩
  | 8 => ⟨((-16335692511/144115188075855872), (-6982103769/144115188075855872)), (6030829/72057594037927936), by norm_num⟩
  | 9 => ⟨((-87336479/144115188075855872), (-6438160865/144115188075855872)), (7350639/288230376151711744), by norm_num⟩
  | 10 => ⟨((24108998679/4611686018427387904), (258184409/2305843009213693952)), (16487231/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-17828214971/36893488147419103232), (15292470335/36893488147419103232)), (34710433/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-3504011585/147573952589676412928), (-583322131/4611686018427387904)), (17956677/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile012Gamma
