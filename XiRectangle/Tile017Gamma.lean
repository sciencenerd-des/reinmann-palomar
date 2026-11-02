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
namespace Reinmann.XiRectangle.Tile017Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/128))
  have he : value ((3/4), (987/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((876544/12697945), (-252672/12697945)), 0, by norm_num⟩
  | 1 => ⟨((-352243122176/161237807223025), (221478125568/161237807223025)), 0, by norm_num⟩
  | 2 => ⟨((8688572449/140737488355328), (-9731427607/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-1624532717/1125899906842624), (13514480913/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((359296989/18014398509481984), (-1062213837/9007199254740992)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((2236267559/4611686018427387904), (19686346361/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-4368817423/73786976294838206464), (-21031316911/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((8173257203/2361183241434822606848), (10223461499/2361183241434822606848)), (5/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-1535272365/9444732965739290427392), (-8689482391/75557863725914323419136)), (15/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((8166020019/1208925819614629174706176), (2843515823/1208925819614629174706176)), (11/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-9924569913/38685626227668133590597632), (-1081477983/77371252455336267181195264)), (1/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((1391713669/154742504910672534362390528), (-5125060877/2475880078570760549798248448)), (23/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-11481172979/39614081257132168796771975168), (6375012385/39614081257132168796771975168)), (17/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (987/256)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (987/256)))⁻¹=value ((876544/12697945), (-252672/12697945)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((876544/12697945), (-252672/12697945))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22619856887/8589934592), (2410774197/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((438272/12697945), (-126336/12697945)), 0, by norm_num⟩
  | 2 => ⟨((-88060780544/161237807223025), (55369531392/161237807223025)), 0, by norm_num⟩
  | 3 => ⟨((11584763265/1125899906842624), (-12975236809/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-1624532717/9007199254740992), (13514480913/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((4599001459/2305843009213693952), (-27192674227/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 6 => ⟨((2981690079/73786976294838206464), (26248461815/73786976294838206464)), (3/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-9985868395/2361183241434822606848), (-24035790755/2361183241434822606848)), (15/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((8173257203/37778931862957161709568), (10223461499/37778931862957161709568)), (5/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-10917492373/1208925819614629174706176), (-1930996087/302231454903657293676544)), (15/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((6532816015/19342813113834066795298816), (4549625317/38685626227668133590597632)), (19/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-28871476111/2475880078570760549798248448), (-393264721/618970019642690137449562112)), (3/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((14844945803/39614081257132168796771975168), (-3416707251/39614081257132168796771975168)), (1/1237940039285380274899124224), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (21/4096)), 0, by norm_num⟩
  | 45 => ⟨((20506076461/816127672320), (-41727/6029312)), 0, by norm_num⟩
  | 44 => ⟨((-9645557370587/383035920875520), (170461457467/23708219473920)), 0, by norm_num⟩
  | 43 => ⟨((3525950761/137438953472), (-1992204393/274877906944)), (1/549755813888), by norm_num⟩
  | 42 => ⟨((-451350597/17179869184), (2026120155/274877906944)), (1/274877906944), by norm_num⟩
  | 41 => ⟨((7400906827/274877906944), (-518144615/68719476736)), (1/549755813888), by norm_num⟩
  | 40 => ⟨((-7586736357/274877906944), (4246810431/549755813888)), (1/549755813888), by norm_num⟩
  | 39 => ⟨((15562360481/549755813888), (-2176522727/274877906944)), (1/549755813888), by norm_num⟩
  | 38 => ⟨((-15971518607/549755813888), (4464183677/549755813888)), (1/549755813888), by norm_num⟩
  | 37 => ⟨((8201436235/274877906944), (-2290505407/274877906944)), (1/274877906944), by norm_num⟩
  | 36 => ⟨((-16858219593/549755813888), (4704119725/549755813888)), (1/274877906944), by norm_num⟩
  | 35 => ⟨((8669786979/274877906944), (-4834040819/549755813888)), (1/274877906944), by norm_num⟩
  | 34 => ⟨((-4462304791/137438953472), (2485673209/274877906944)), (1/274877906944), by norm_num⟩
  | 33 => ⟨((4489679/134217728), (-2558340345/274877906944)), (1/274877906944), by norm_num⟩
  | 32 => ⟨((-18963983315/549755813888), (5270768599/549755813888)), (1/274877906944), by norm_num⟩
  | 31 => ⟨((19575256799/549755813888), (-5434425789/549755813888)), (1/274877906944), by norm_num⟩
  | 30 => ⟨((-10113621595/274877906944), (2804286205/274877906944)), (1/274877906944), by norm_num⟩
  | 29 => ⟨((5231037347/137438953472), (-1448562603/137438953472)), (1/274877906944), by norm_num⟩
  | 28 => ⟨((-21670782507/549755813888), (374540279/34359738368)), (1/274877906944), by norm_num⟩
  | 27 => ⟨((11236330427/274877906944), (-6205107279/549755813888)), (1/549755813888), by norm_num⟩
  | 26 => ⟨((-5834037619/137438953472), (1608297629/137438953472)), (1/549755813888), by norm_num⟩
  | 25 => ⟨((24268634431/549755813888), (-6678682751/549755813888)), (1/274877906944), by norm_num⟩
  | 24 => ⟨((-6319681073/137438953472), (1735914123/137438953472)), (1/274877906944), by norm_num⟩
  | 23 => ⟨((26376526731/549755813888), (-7230526865/549755813888)), (1/274877906944), by norm_num⟩
  | 22 => ⟨((-13786991325/274877906944), (235691421/17179869184)), (1/274877906944), by norm_num⟩
  | 21 => ⟨((1805331437/34359738368), (-1970448559/137438953472)), (1/274877906944), by norm_num⟩
  | 20 => ⟨((-15163767503/274877906944), (4126752903/274877906944)), (1/274877906944), by norm_num⟩
  | 19 => ⟨((7980326719/137438953472), (-2165504941/137438953472)), (1/274877906944), by norm_num⟩
  | 18 => ⟨((-4211477489/68719476736), (1139135961/68719476736)), (1/137438953472), by norm_num⟩
  | 17 => ⟨((17835094971/274877906944), (-4806862937/274877906944)), (1/274877906944), by norm_num⟩
  | 16 => ⟨((-592113909/8589934592), (2543145829/137438953472)), (1/274877906944), by norm_num⟩
  | 15 => ⟨((10104082205/137438953472), (-2700111535/137438953472)), (1/137438953472), by norm_num⟩
  | 14 => ⟨((-1353016483/17179869184), (2877735373/137438953472)), (1/137438953472), by norm_num⟩
  | 13 => ⟨((11654622649/137438953472), (-770096211/34359738368)), (1/137438953472), by norm_num⟩
  | 12 => ⟨((-6311531091/68719476736), (3313752727/137438953472)), (1/274877906944), by norm_num⟩
  | 11 => ⟨((13766917075/137438953472), (-1792700709/68719476736)), (1/68719476736), by norm_num⟩
  | 10 => ⟨((-15138567485/137438953472), (3905599831/137438953472)), (1/68719476736), by norm_num⟩
  | 9 => ⟨((16813546177/137438953472), (-1072163647/34359738368)), (1/68719476736), by norm_num⟩
  | 8 => ⟨((-18904918245/137438953472), (148597305/4294967296)), (1/68719476736), by norm_num⟩
  | 7 => ⟨((5397474957/34359738368), (-2667796723/68719476736)), (1/68719476736), by norm_num⟩
  | 6 => ⟨((-6290721081/34359738368), (3038909903/68719476736)), (1/68719476736), by norm_num⟩
  | 5 => ⟨((15075761817/68719476736), (-1765140487/34359738368)), (1/34359738368), by norm_num⟩
  | 4 => ⟨((-18802555859/68719476736), (2105972379/34359738368)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((24976347729/68719476736), (-5221813845/68719476736)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-18599568331/34359738368), (859396793/8589934592)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((18291442839/17179869184), (-2522928775/17179869184)), (1/17179869184), by norm_num⟩
  | 0 => ⟨((-2392997775/17179869184), (19286193573/68719476736)), (3/68719476736), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (987/4096)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (987/4096)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (987/4096))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((22619856887/8589934592), (2410774197/8589934592)), (1/8589934592), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (987/256))) (z:=((-21/128), (987/4096))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((22619856887/8589934592), (2410774197/8589934592))) (r:=(1/8589934592)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((17620999553/536870912), (7390554321/536870912)), (3/536870912), by norm_num⟩
  | 1 => ⟨((7728327061/4294967296), (624059565/4294967296)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((1435318828032/161237807223025), (-428736660576/161237807223025)), 0, by norm_num⟩
  | 3 => ⟨((-6767393499/70368744177664), (1108237003/17592186044416)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((3099257405/2251799813685248), (-14664546921/9007199254740992)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((-5485942285/288230376151711744), (12511126869/288230376151711744)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((168330607/1152921504606846976), (-21409507211/18446744073709551616)), (87/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1476028227/295147905179352825856), (18003594883/590295810358705651712)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-7036248499/18889465931478580854784), (-7286880377/9444732965739290427392)), (145/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((2498622653/151115727451828646838272), (1377314677/75557863725914323419136)), (207/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-3000100477/4835703278458516698824704), (-3658296905/9671406556917033397649408)), (35/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((6555606175/309485009821345068724781056), (3505450775/618970019642690137449562112)), (353/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-3333765455/4951760157141521099596496896), (329823855/19807040628566084398385987584)), (115/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((10440351105/536870912), (5320665297/536870912)), (3/536870912), by norm_num⟩
  | 1 => ⟨((5580843413/4294967296), (624059565/4294967296)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((1435318828032/161237807223025), (-428736660576/161237807223025)), 0, by norm_num⟩
  | 3 => ⟨((-6767393499/70368744177664), (1108237003/17592186044416)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((3099257405/2251799813685248), (-14664546921/9007199254740992)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((-5485942285/288230376151711744), (12511126869/288230376151711744)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((168330607/1152921504606846976), (-21409507211/18446744073709551616)), (87/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1476028227/295147905179352825856), (18003594883/590295810358705651712)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-7036248499/18889465931478580854784), (-7286880377/9444732965739290427392)), (145/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((2498622653/151115727451828646838272), (1377314677/75557863725914323419136)), (207/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-3000100477/4835703278458516698824704), (-3658296905/9671406556917033397649408)), (35/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((6555606175/309485009821345068724781056), (3505450775/618970019642690137449562112)), (353/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-3333765455/4951760157141521099596496896), (329823855/19807040628566084398385987584)), (115/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((21867404947/1073741824), (5320665297/536870912)), (7/1073741824), by norm_num⟩
  | 1 => ⟨((5580843413/4294967296), (624059565/4294967296)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((1435318828032/161237807223025), (-428736660576/161237807223025)), 0, by norm_num⟩
  | 3 => ⟨((-6767393499/70368744177664), (1108237003/17592186044416)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((3099257405/2251799813685248), (-14664546921/9007199254740992)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((-5485942285/288230376151711744), (12511126869/288230376151711744)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((168330607/1152921504606846976), (-21409507211/18446744073709551616)), (87/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1476028227/295147905179352825856), (18003594883/590295810358705651712)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-7036248499/18889465931478580854784), (-7286880377/9444732965739290427392)), (145/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((2498622653/151115727451828646838272), (1377314677/75557863725914323419136)), (207/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-3000100477/4835703278458516698824704), (-3658296905/9671406556917033397649408)), (35/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((6555606175/309485009821345068724781056), (3505450775/618970019642690137449562112)), (353/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-3333765455/4951760157141521099596496896), (329823855/19807040628566084398385987584)), (115/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((704486244352/161237807223025), (-442956251136/161237807223025)), 0, by norm_num⟩
  | 1 => ⟨((-8688572449/35184372088832), (9731427607/35184372088832)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((9747196301/1125899906842624), (-20271721369/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 3 => ⟨((-359296989/2251799813685248), (16995421391/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((-2795334449/576460752303423488), (-24607932951/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((6553226135/9223372036854775808), (15773487683/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-7151600053/147573952589676412928), (-2236382203/36893488147419103232)), (7/147573952589676412928), by norm_num⟩
  | 7 => ⟨((12282178921/4722366482869645213696), (8689482391/4722366482869645213696)), (3/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-4593386261/37778931862957161709568), (-3198955301/75557863725914323419136)), (19/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((1550714049/302231454903657293676544), (675923739/2417851639229258349412352)), (15/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-1913606295/9671406556917033397649408), (3523479353/77371252455336267181195264)), (3/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((8610879735/1237940039285380274899124224), (-4781259289/1237940039285380274899124224)), (9/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-8654042845/39614081257132168796771975168), (8690882449/39614081257132168796771975168)), (7/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8688572449/35184372088832), (-9731427607/35184372088832)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-9747196301/562949953421312), (20271721369/562949953421312)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((4311563867/9007199254740992), (-12746566043/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((2795334449/144115188075855872), (12303966475/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 4 => ⟨((-2047883167/576460752303423488), (-19716859603/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 5 => ⟨((670462505/2305843009213693952), (6709146609/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-2686726639/147573952589676412928), (-1900824273/147573952589676412928)), (9/590295810358705651712), by norm_num⟩
  | 7 => ⟨((18373545045/18889465931478580854784), (6397910601/18889465931478580854784)), (17/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-27912852883/604462909807314587353088), (-1520828413/604462909807314587353088)), (29/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((9568031475/4835703278458516698824704), (-550543649/1208925819614629174706176)), (25/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-2959989909/38685626227668133590597632), (6574231523/154742504910672534362390528)), (5/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((12981064267/4951760157141521099596496896), (-13036323675/4951760157141521099596496896)), (33/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-5942370481/79228162514264337593543950336), (21619884559/158456325028528675187087900672)), (51/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1624532717/140737488355328), (-13514480913/562949953421312)), (3/562949953421312), by norm_num⟩
  | 1 => ⟨((-2874375911/4503599627370496), (16995421391/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 2 => ⟨((-1397667225/36028797018963968), (-12303966475/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 3 => ⟨((5461021779/576460752303423488), (3286143267/144115188075855872)), (5/576460752303423488), by norm_num⟩
  | 4 => ⟨((-4469750033/4611686018427387904), (-5590955507/4611686018427387904)), (7/9223372036854775808), by norm_num⟩
  | 5 => ⟨((2686726639/36893488147419103232), (1900824273/36893488147419103232)), (9/147573952589676412928), by norm_num⟩
  | 6 => ⟨((-2679475319/590295810358705651712), (-7464229035/4722366482869645213696)), (9/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((18608568589/75557863725914323419136), (126735701/9444732965739290427392)), (9/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-14352047213/1208925819614629174706176), (1651630947/604462909807314587353088)), (17/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((4933316515/9671406556917033397649408), (-10957052539/38685626227668133590597632)), (31/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-743706807/38685626227668133590597632), (11949963369/618970019642690137449562112)), (27/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((5942370481/9903520314283042199192993792), (-1351242785/1237940039285380274899124224)), (23/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-1951008179/158456325028528675187087900672), (17289192353/316912650057057350374175801344)), (19/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359296989/1125899906842624), (-1062213837/562949953421312)), (5/9007199254740992), by norm_num⟩
  | 1 => ⟨((1397667225/36028797018963968), (12303966475/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 2 => ⟨((-8191532669/576460752303423488), (-9858429801/288230376151711744)), (7/576460752303423488), by norm_num⟩
  | 3 => ⟨((4469750033/2305843009213693952), (5590955507/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-6716816597/36893488147419103232), (-2376030341/18446744073709551616)), (5/36893488147419103232), by norm_num⟩
  | 5 => ⟨((16076851913/1180591620717411303424), (43735717/9223372036854775808)), (7/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-16282497515/18889465931478580854784), (-887149907/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((14352047213/302231454903657293676544), (-3303261895/302231454903657293676544)), (17/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-11099962159/4835703278458516698824704), (6163342053/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((3718534035/38685626227668133590597632), (-14937454211/154742504910672534362390528)), (33/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((-8170759411/2475880078570760549798248448), (14863670635/2475880078570760549798248448)), (15/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((5853024537/79228162514264337593543950336), (-25933788531/79228162514264337593543950336)), (27/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((1194783293/1267650600228229401496703205376), (20337990879/1267650600228229401496703205376)), (47/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2236267559/144115188075855872), (-19686346361/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 1 => ⟨((6553226135/576460752303423488), (7886743841/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 2 => ⟨((-670462505/288230376151711744), (-419321663/144115188075855872)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((10746906555/36893488147419103232), (7603297091/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-16076851913/590295810358705651712), (-5598171775/590295810358705651712)), (13/590295810358705651712), by norm_num⟩
  | 5 => ⟨((19538997017/9444732965739290427392), (66536243/590295810358705651712)), (19/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-20092866097/151115727451828646838272), (1156141663/37778931862957161709568)), (23/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((8879969727/1208925819614629174706176), (-9861347285/2417851639229258349412352)), (7/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-13386722525/38685626227668133590597632), (6721854395/19342813113834066795298816)), (15/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((8170759411/618970019642690137449562112), (-14863670635/618970019642690137449562112)), (15/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-3219163495/9903520314283042199192993792), (3565895923/2475880078570760549798248448)), (15/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-89608747/19807040628566084398385987584), (-24405589055/316912650057057350374175801344)), (7/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((6625579575/5070602400912917605986812821504), (2346280009/633825300114114700748351602688)), (13/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4368817423/1152921504606846976), (-21031316911/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 1 => ⟨((7151600053/4611686018427387904), (8945528811/4611686018427387904)), (11/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-2686726639/9223372036854775808), (-7603297091/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 3 => ⟨((10717901275/295147905179352825856), (7464229033/590295810358705651712)), (17/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-32564995027/9444732965739290427392), (-1774299813/9444732965739290427392)), (15/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((1255804131/4722366482869645213696), (-1156141663/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-20719929361/1208925819614629174706176), (5752452583/604462909807314587353088)), (1/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((8924481683/9671406556917033397649408), (-8962472527/9671406556917033397649408)), (21/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-3064034779/77371252455336267181195264), (696734561/9671406556917033397649408)), (3/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((5365272491/4951760157141521099596496896), (-11886319743/2475880078570760549798248448)), (51/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((1314261623/79228162514264337593543950336), (22371789967/79228162514264337593543950336)), (53/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-6625579575/1267650600228229401496703205376), (-2346280009/158456325028528675187087900672)), (53/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((9970425409/20282409603651670423947251286016), (6983260459/10141204801825835211973625643008)), (51/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8173257203/18446744073709551616), (-10223461499/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 1 => ⟨((12282178921/73786976294838206464), (4344741195/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-4593386261/147573952589676412928), (-799738825/73786976294838206464)), (15/590295810358705651712), by norm_num⟩
  | 3 => ⟨((18608568587/4722366482869645213696), (1013885607/4722366482869645213696)), (17/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((-14352047211/37778931862957161709568), (3303261895/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((4439984863/151115727451828646838272), (-9861347285/604462909807314587353088)), (7/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-8924481683/4835703278458516698824704), (4481236263/2417851639229258349412352)), (21/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((3501754033/38685626227668133590597632), (-12740289115/77371252455336267181195264)), (29/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-26946123/9671406556917033397649408), (7641205549/618970019642690137449562112)), (35/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-1877516605/39614081257132168796771975168), (-1997481247/2475880078570760549798248448)), (5/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((5205812523/316912650057057350374175801344), (7374022885/158456325028528675187087900672)), (11/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-4273039461/2535301200456458802993406410752), (-2992825911/1267650600228229401496703205376)), (23/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((10489924225/81129638414606681695789005144064), (8313490675/81129638414606681695789005144064)), (47/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1535272365/36893488147419103232), (-8689482391/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 1 => ⟨((4593386261/295147905179352825856), (799738825/147573952589676412928)), (17/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((-13956426441/4722366482869645213696), (-1520828411/9444732965739290427392)), (7/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((14352047211/37778931862957161709568), (-3303261895/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((-11099962157/302231454903657293676544), (6163342053/302231454903657293676544)), (9/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((13386722523/4835703278458516698824704), (-6721854395/2417851639229258349412352)), (1/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-6128069557/38685626227668133590597632), (11147752975/38685626227668133590597632)), (13/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((26946123/4835703278458516698824704), (-15282411097/618970019642690137449562112)), (37/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((528051545/4951760157141521099596496896), (17977331223/9903520314283042199192993792)), (49/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-3253632827/79228162514264337593543950336), (-4608764303/39614081257132168796771975168)), (59/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((5875429259/1267650600228229401496703205376), (16460542509/2535301200456458802993406410752)), (17/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-7867443169/20282409603651670423947251286016), (-3117559003/10141204801825835211973625643008)), (75/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((17791014933/649037107316853453566312041152512), (114108775/10141204801825835211973625643008)), (5/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8166020019/2361183241434822606848), (-2843515823/2361183241434822606848)), (11/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((1550714049/1180591620717411303424), (337961869/4722366482869645213696)), (29/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((-19136062949/75557863725914323419136), (4404349193/75557863725914323419136)), (25/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((19733266057/604462909807314587353088), (-10957052539/604462909807314587353088)), (33/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((-14874136137/4835703278458516698824704), (7468727105/2417851639229258349412352)), (37/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((8170759409/38685626227668133590597632), (-7431835317/19342813113834066795298816)), (35/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-2682636245/309485009821345068724781056), (23772639483/618970019642690137449562112)), (15/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((-1877516605/9903520314283042199192993792), (-31959699949/9903520314283042199192993792)), (45/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((3253632827/39614081257132168796771975168), (4608764303/19807040628566084398385987584)), (1/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-1632063683/158456325028528675187087900672), (-4572372919/316912650057057350374175801344)), (41/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((9615763873/10141204801825835211973625643008), (7620699785/10141204801825835211973625643008)), (25/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-5930338311/81129638414606681695789005144064), (-2434320533/81129638414606681695789005144064)), (57/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((801173137/162259276829213363391578010288128), (1401017349/2596148429267413814265248164610048)), (127/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9924569913/37778931862957161709568), (-1081477983/75557863725914323419136)), (1/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((15308850359/151115727451828646838272), (-3523479355/151115727451828646838272)), (3/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((-11839959635/604462909807314587353088), (6574231523/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 3 => ⟨((5949654455/2417851639229258349412352), (-1493745421/604462909807314587353088)), (1/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-8170759409/38685626227668133590597632), (14863670633/38685626227668133590597632)), (37/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((1609581747/154742504910672534362390528), (-7131791845/154742504910672534362390528)), (37/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((164282703/618970019642690137449562112), (5592947491/1237940039285380274899124224)), (33/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((-5205812523/39614081257132168796771975168), (-1843505721/4951760157141521099596496896)), (27/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((11750858517/633825300114114700748351602688), (4115135627/158456325028528675187087900672)), (79/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((-9615763873/5070602400912917605986812821504), (-7620699785/5070602400912917605986812821504)), (55/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((3261686071/20282409603651670423947251286016), (1338876293/20282409603651670423947251286016)), (69/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((-7691262115/649037107316853453566312041152512), (-840610409/649037107316853453566312041152512)), (83/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((8032314111/10384593717069655257060992658440192), (-1393598757/10384593717069655257060992658440192)), (3/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((219136/38093835), (-21056/12697945)), 0, by norm_num⟩
  | 1 => ⟨((-88060780544/483713421669075), (18456510464/161237807223025)), 0, by norm_num⟩
  | 2 => ⟨((11584763265/2251799813685248), (-12975236809/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-8664174491/72057594037927936), (4504826971/18014398509481984)), (5/72057594037927936), by norm_num⟩
  | 4 => ⟨((119765663/72057594037927936), (-354071279/36028797018963968)), (7/2305843009213693952), by norm_num⟩
  | 5 => ⟨((2981690079/73786976294838206464), (26248461815/73786976294838206464)), (3/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-5825089897/1180591620717411303424), (-14020877941/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((10897676271/37778931862957161709568), (13631281999/37778931862957161709568)), (7/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-511757455/37778931862957161709568), (-11585976521/1208925819614629174706176)), (21/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((2722006673/4835703278458516698824704), (7582708861/38685626227668133590597632)), (15/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-3308189971/154742504910672534362390528), (-360492661/309485009821345068724781056)), (43/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((14844945803/19807040628566084398385987584), (-3416707251/19807040628566084398385987584)), (1/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-15308230639/633825300114114700748351602688), (8500016513/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21873581681/1073741824), (10639550093/1073741824)), (1/134217728), by norm_num⟩
  | 1 => ⟨((11160123015/8589934592), (2498204799/17179869184)), (3/17179869184), by norm_num⟩
  | 2 => ⟨((4896685925/549755813888), (-5859946675/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-6775854607/70368744177664), (8901089985/140737488355328)), (7/140737488355328), by norm_num⟩
  | 4 => ⟨((1551500041/1125899906842624), (-14753064741/9007199254740992)), (23/9007199254740992), by norm_num⟩
  | 5 => ⟨((-2737147529/144115188075855872), (12613659923/288230376151711744)), (33/288230376151711744), by norm_num⟩
  | 6 => ⟨((1301136341/9223372036854775808), (-21628583429/18446744073709551616)), (11/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1561166323/295147905179352825856), (1138536479/36893488147419103232)), (113/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-3646063613/9444732965739290427392), (-14754791637/18889465931478580854784)), (73/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5167370723/302231454903657293676544), (5568498621/302231454903657293676544)), (13/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-6206962827/9671406556917033397649408), (-7339124601/19342813113834066795298816)), (141/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((27150233813/1237940039285380274899124224), (6797357347/1237940039285380274899124224)), (709/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-27626888055/39614081257132168796771975168), (595449371/19807040628566084398385987584)), (923/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-772317551/1125899906842624), (13840252597/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 1 => ⟨((866417449/18014398509481984), (-14415446307/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 2 => ⟨((-766500243/576460752303423488), (18128449483/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((-993896693/18446744073709551616), (-8749487271/18446744073709551616)), (3/18446744073709551616), by norm_num⟩
  | 4 => ⟨((5825089897/590295810358705651712), (3505219485/147573952589676412928)), (7/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-3814186695/4722366482869645213696), (-19083794799/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((3821122331/75557863725914323419136), (5406789043/151115727451828646838272)), (7/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-408301001/151115727451828646838272), (-1137406329/1208925819614629174706176)), (13/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((4962284957/38685626227668133590597632), (1081477983/154742504910672534362390528)), (11/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-27215733973/4951760157141521099596496896), (6263963295/4951760157141521099596496896)), (37/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((16839053705/79228162514264337593543950336), (-4675009083/39614081257132168796771975168)), (29/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-4615489517/633825300114114700748351602688), (9270274613/1267650600228229401496703205376)), (25/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((8451371351/40564819207303340847894502572032), (-15374140131/40564819207303340847894502572032)), (37/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1367098809/67108864), (5319775459/536870912)), (9/1073741824), by norm_num⟩
  | 1 => ⟨((2790030857/2147483648), (2498203081/17179869184)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((2448342597/274877906944), (-2929964693/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-13551716797/140737488355328), (17384811/274877906944)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((3103022303/2251799813685248), (-14752850799/9007199254740992)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-5474527857/288230376151711744), (12613368727/288230376151711744)), (17/144115188075855872), by norm_num⟩
  | 6 => ⟨((2603205573/18446744073709551616), (-21627923421/18446744073709551616)), (89/18446744073709551616), by norm_num⟩
  | 7 => ⟨((390092215/73786976294838206464), (9108014145/295147905179352825856)), (57/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-7289704235/18889465931478580854784), (-14754659621/18889465931478580854784)), (147/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((10331419213/604462909807314587353088), (5568880943/302231454903657293676544)), (209/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-12409814557/19342813113834066795298816), (-917675915/2417851639229258349412352)), (283/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((27141219185/1237940039285380274899124224), (3403205175/618970019642690137449562112)), (355/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-27618634763/39614081257132168796771975168), (1175884933/39614081257132168796771975168)), (231/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2336000741/9223372036854775808), (-27624303977/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 1 => ⟨((1135881935/36893488147419103232), (1249926753/4611686018427387904)), (3/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-3328622799/295147905179352825856), (-8011930251/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 3 => ⟨((3632558757/2361183241434822606848), (2271880333/1180591620717411303424)), (3/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-5458746187/37778931862957161709568), (-7723984347/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((13065632031/1208925819614629174706176), (1137406329/302231454903657293676544)), (3/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-13232759885/19342813113834066795298816), (-720985321/19342813113834066795298816)), (13/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((11663885989/309485009821345068724781056), (-2684555699/309485009821345068724781056)), (29/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-18041843255/9903520314283042199192993792), (10017876607/9903520314283042199192993792)), (29/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((12088186831/158456325028528675187087900672), (-12139645327/158456325028528675187087900672)), (7/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-1660090801/633825300114114700748351602688), (3019920383/633825300114114700748351602688)), (25/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((4756743751/81129638414606681695789005144064), (-10538174387/40564819207303340847894502572032)), (45/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((485499243/649037107316853453566312041152512), (16528652905/1298074214633706907132624082305024)), (39/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1367098809/67108864), (2659887729/268435456)), (5/536870912), by norm_num⟩
  | 1 => ⟨((22320246857/17179869184), (1249101543/8589934592)), (5/17179869184), by norm_num⟩
  | 2 => ⟨((19586740751/2199023255552), (-2929964723/1099511627776)), (3/2199023255552), by norm_num⟩
  | 3 => ⟨((-3387929145/35184372088832), (8901023503/140737488355328)), (9/140737488355328), by norm_num⟩
  | 4 => ⟨((12412087911/9007199254740992), (-1844106465/1125899906842624)), (25/9007199254740992), by norm_num⟩
  | 5 => ⟨((-2737262371/144115188075855872), (3153342453/72057594037927936)), (35/288230376151711744), by norm_num⟩
  | 6 => ⟨((2603192953/18446744073709551616), (-21627924109/18446744073709551616)), (45/9223372036854775808), by norm_num⟩
  | 7 => ⟨((3120759967/590295810358705651712), (9108011585/295147905179352825856)), (115/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-7289738647/18889465931478580854784), (-14754640513/18889465931478580854784)), (37/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5165732663/302231454903657293676544), (11137715577/604462909807314587353088)), (105/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-12409865219/19342813113834066795298816), (-7341315159/19342813113834066795298816)), (71/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((27141291767/1237940039285380274899124224), (3403044375/618970019642690137449562112)), (711/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-13809302565/19807040628566084398385987584), (1176389347/39614081257132168796771975168)), (925/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2662898239/1180591620717411303424), (12819088403/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-8718141017/9444732965739290427392), (-5452512799/4722366482869645213696)), (7/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((13100990849/75557863725914323419136), (289649413/2361183241434822606848)), (11/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-6532816015/302231454903657293676544), (-4549625315/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((9924569913/4835703278458516698824704), (1081477981/9671406556917033397649408)), (19/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-12247080287/77371252455336267181195264), (2818783483/77371252455336267181195264)), (15/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((12629290277/1237940039285380274899124224), (-7012513625/1237940039285380274899124224)), (5/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-10879368147/19807040628566084398385987584), (10925680795/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((1867602151/79228162514264337593543950336), (-13589641723/316912650057057350374175801344)), (15/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((-204391333/316912650057057350374175801344), (7244994891/2535301200456458802993406410752)), (1/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-801073751/81129638414606681695789005144064), (-27272277293/162259276829213363391578010288128)), (33/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((4038448503/1298074214633706907132624082305024), (22881816469/2596148429267413814265248164610048)), (33/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((-3038605839/10384593717069655257060992658440192), (-17025854071/41538374868278621028243970633760768)), (63/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1367098809/67108864), (2659887729/268435456)), (11/1073741824), by norm_num⟩
  | 1 => ⟨((22320246857/17179869184), (1249101543/8589934592)), (3/8589934592), by norm_num⟩
  | 2 => ⟨((19586740751/2199023255552), (-2929964723/1099511627776)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-13551716583/140737488355328), (4450511751/70368744177664)), (5/70368744177664), by norm_num⟩
  | 4 => ⟨((12412087929/9007199254740992), (-14752851719/9007199254740992)), (13/4503599627370496), by norm_num⟩
  | 5 => ⟨((-1368631197/72057594037927936), (12613369823/288230376151711744)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((2603193141/18446744073709551616), (-21627924213/18446744073709551616)), (91/18446744073709551616), by norm_num⟩
  | 7 => ⟨((3120759643/590295810358705651712), (2277002937/73786976294838206464)), (29/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-3644869101/9444732965739290427392), (-14754641323/18889465931478580854784)), (149/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1291433117/75557863725914323419136), (1392214663/75557863725914323419136)), (211/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-6204932705/9671406556917033397649408), (-3670659205/9671406556917033397649408)), (285/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((13570647809/618970019642690137449562112), (6806099661/1237940039285380274899124224)), (89/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-27618616721/39614081257132168796771975168), (588186555/19807040628566084398385987584)), (463/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10586659271/302231454903657293676544), (-936240527/37778931862957161709568)), (7/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((15837129735/1208925819614629174706176), (689337169/151115727451828646838272)), (15/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((-24059563427/9671406556917033397649408), (-1310882401/9671406556917033397649408)), (25/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((24741576337/77371252455336267181195264), (-711814011/9671406556917033397649408)), (15/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((-9567644149/309485009821345068724781056), (2656255161/154742504910672534362390528)), (1/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((11538723791/4951760157141521099596496896), (-11587843267/4951760157141521099596496896)), (7/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-5282107093/39614081257132168796771975168), (9608837581/39614081257132168796771975168)), (23/39614081257132168796771975168), by norm_num⟩
  | 7 => ⟨((5945929687/1267650600228229401496703205376), (-26345435965/1267650600228229401496703205376)), (65/1267650600228229401496703205376), by norm_num⟩
  | 8 => ⟨((910311081/10141204801825835211973625643008), (7747806049/5070602400912917605986812821504)), (85/20282409603651670423947251286016), by norm_num⟩
  | 9 => ⟨((-2804478127/81129638414606681695789005144064), (-3972537581/40564819207303340847894502572032)), (13/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((5064343065/1298074214633706907132624082305024), (14188211725/2596148429267413814265248164610048)), (59/2596148429267413814265248164610048), by norm_num⟩
  | 11 => ⟨((-1695341289/5192296858534827628530496329220096), (-2687188905/10384593717069655257060992658440192)), (33/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((15335016239/664613997892457936451903530140172288), (1573702163/166153499473114484112975882535043072)), (35/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1367098809/67108864), (2659887729/268435456)), (3/268435456), by norm_num⟩
  | 1 => ⟨((22320246857/17179869184), (1249101543/8589934592)), (7/17179869184), by norm_num⟩
  | 2 => ⟨((19586740751/2199023255552), (-2929964723/1099511627776)), (5/2199023255552), by norm_num⟩
  | 3 => ⟨((-13551716583/140737488355328), (4450511751/70368744177664)), (11/140737488355328), by norm_num⟩
  | 4 => ⟨((12412087929/9007199254740992), (-14752851719/9007199254740992)), (27/9007199254740992), by norm_num⟩
  | 5 => ⟨((-5474524787/288230376151711744), (6306684911/144115188075855872)), (37/288230376151711744), by norm_num⟩
  | 6 => ⟨((2603193139/18446744073709551616), (-21627924209/18446744073709551616)), (23/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1560379823/295147905179352825856), (4554005871/147573952589676412928)), (117/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-911217275/2361183241434822606848), (-7377320647/9444732965739290427392)), (75/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((10331464915/604462909807314587353088), (11137717245/604462909807314587353088)), (53/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-12409865335/19342813113834066795298816), (-229416197/604462909807314587353088)), (143/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((13570647607/618970019642690137449562112), (6806099341/1237940039285380274899124224)), (713/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-27618615807/39614081257132168796771975168), (1176373485/39614081257132168796771975168)), (927/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1217960317/2417851639229258349412352), (1061766729/38685626227668133590597632)), (1/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((-1878728489/9671406556917033397649408), (3459259651/77371252455336267181195264)), (25/77371252455336267181195264), by norm_num⟩
  | 2 => ⟨((11624161947/309485009821345068724781056), (-6454408145/309485009821345068724781056)), (3/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((-11682429509/2475880078570760549798248448), (1466520091/309485009821345068724781056)), (1/77371252455336267181195264), by norm_num⟩
  | 4 => ⟨((8021837365/19807040628566084398385987584), (-912047633/1237940039285380274899124224)), (37/19807040628566084398385987584), by norm_num⟩
  | 5 => ⟨((-6320980635/316912650057057350374175801344), (14003612501/158456325028528675187087900672)), (73/316912650057057350374175801344), by norm_num⟩
  | 6 => ⟨((-1290307605/2535301200456458802993406410752), (-10982018419/1267650600228229401496703205376)), (65/2535301200456458802993406410752), by norm_num⟩
  | 7 => ⟨((638866281/2535301200456458802993406410752), (14479244667/20282409603651670423947251286016)), (27/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((-11536684805/324518553658426726783156020576256), (-4040132267/81129638414606681695789005144064)), (79/324518553658426726783156020576256), by norm_num⟩
  | 9 => ⟨((4720252431/1298074214633706907132624082305024), (14963606495/5192296858534827628530496329220096)), (109/5192296858534827628530496329220096), by norm_num⟩
  | 10 => ⟨((-3202237869/10384593717069655257060992658440192), (-2628947283/20769187434139310514121985316880384)), (69/41538374868278621028243970633760768), by norm_num⟩
  | 11 => ⟨((30204317973/1329227995784915872903807060280344576), (3301157041/1329227995784915872903807060280344576)), (41/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((-7885915401/5316911983139663491615228241121378304), (684099361/2658455991569831745807614120560689152)), (95/10633823966279326983230456482242756608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1367098809/67108864), (2659887729/268435456)), (13/1073741824), by norm_num⟩
  | 1 => ⟨((22320246857/17179869184), (1249101543/8589934592)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((19586740751/2199023255552), (-2929964723/1099511627776)), (3/1099511627776), by norm_num⟩
  | 3 => ⟨((-13551716583/140737488355328), (4450511751/70368744177664)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((12412087929/9007199254740992), (-14752851719/9007199254740992)), (7/2251799813685248), by norm_num⟩
  | 5 => ⟨((-5474524787/288230376151711744), (6306684911/144115188075855872)), (19/144115188075855872), by norm_num⟩
  | 6 => ⟨((2603193139/18446744073709551616), (-21627924209/18446744073709551616)), (93/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1560379823/295147905179352825856), (4554005871/147573952589676412928)), (59/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-7289738201/18889465931478580854784), (-14754641295/18889465931478580854784)), (151/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((10331464917/604462909807314587353088), (11137717247/604462909807314587353088)), (213/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-12409865341/19342813113834066795298816), (-3670659153/9671406556917033397649408)), (287/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((13570647621/618970019642690137449562112), (425381209/77371252455336267181195264)), (357/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-13809307933/19807040628566084398385987584), (1176373495/39614081257132168796771975168)), (29/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-652775724956341/1048576), (-343231186378629/1048576)), (52006289/2097152), by norm_num⟩
  | 1 => ⟨((-12179283461/16), (-8252750607/16)), (581/16), by norm_num⟩
  | 2 => ⟨((-7414359723/16), (-3133326923/8)), (215/8), by norm_num⟩
  | 3 => ⟨((-1496436279/8), (-6201555039/32)), (107/8), by norm_num⟩
  | 4 => ⟨((-14391812949/256), (-18143103661/256)), (645/128), by norm_num⟩
  | 5 => ⟨((-1712577487/128), (-1314303877/64)), (393/256), by norm_num⟩
  | 6 => ⟨((-10710951865/4096), (-10092465671/2048)), (1611/4096), by norm_num⟩
  | 7 => ⟨((-3512129135/8192), (-16541585695/16384)), (1429/16384), by norm_num⟩
  | 8 => ⟨((-7798710351/131072), (-2958432643/16384)), (2239/131072), by norm_num⟩
  | 9 => ⟨((-911119827/131072), (-3758145267/131072)), (1575/524288), by norm_num⟩
  | 10 => ⟨((-693121445/1048576), (-17180788133/4194304)), (1007/2097152), by norm_num⟩
  | 11 => ⟨((-378350283/8388608), (-4463971145/8388608)), (1183/16777216), by norm_num⟩
  | 12 => ⟨((-193651295/268435456), (-1063961595/16777216)), (2573/268435456), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((100656983600993/633825300114114700748351602688), (-1730856083103/5070602400912917605986812821504)), (3943/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1814003123134007/633825300114114700748351602688), (-33191540235/4951760157141521099596496896)), (9719/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((964711307904265/19807040628566084398385987584), (-2396138474967/19807040628566084398385987584)), (1371/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1931717349161401/2475880078570760549798248448), (-2551317357509/1237940039285380274899124224)), (23363/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1813428067788453/154742504910672534362390528), (-639345538327/19342813113834066795298816)), (23427/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((794599156047187/4835703278458516698824704), (-4808017587893/9671406556917033397649408)), (22029/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((323381352876511/151115727451828646838272), (-1054996789615/151115727451828646838272)), (19343/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((486082108395439/18889465931478580854784), (-3440949424697/37778931862957161709568)), (31559/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1340020033539675/4722366482869645213696), (-5182889498705/4722366482869645213696)), (23781/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1679986571781495/590295810358705651712), (-3580769603135/295147905179352825856)), (2055/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1896839952402341/73786976294838206464), (-4502424412735/36893488147419103232)), (1293/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1905458506303273/9223372036854775808), (-10203759363855/9223372036854775808)), (46929/9223372036854775808), by norm_num⟩
  | 6 => ⟨((209630116252283/144115188075855872), (-10296195669419/1152921504606846976)), (47411/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1267632247781349/144115188075855872), (-9114280705049/144115188075855872)), (21017/72057594037927936), by norm_num⟩
  | 4 => ⟨((800988944067803/18014398509481984), (-3471117296155/9007199254740992)), (16041/9007199254740992), by norm_num⟩
  | 3 => ⟨((1628534132101929/9007199254740992), (-17734876746085/9007199254740992)), (82193/9007199254740992), by norm_num⟩
  | 2 => ⟨((1255307422046653/2251799813685248), (-2289619211591/281474976710656)), (85253/2251799813685248), by norm_num⟩
  | 1 => ⟨((165662919454049/140737488355328), (-28977669088557/1125899906842624)), (1061/8796093022208), by norm_num⟩
  | 0 => ⟨((1546544012442025/1125899906842624), (-64255160489963/1125899906842624)), (38133/140737488355328), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1546544012442025/1125899906842624), (-64255160489963/1125899906842624)), (145465851366949037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1060338331258265/562949953421312), (-88261339325383/562949953421312)), (436449/562949953421312), by norm_num⟩
  | 2 => ⟨((495837732080085/140737488355328), (-83121848297637/140737488355328)), (445249/140737488355328), by norm_num⟩
  | 3 => ⟨((53056629065719/4398046511104), (-146424912181705/35184372088832)), (1831647/70368744177664), by norm_num⟩
  | 4 => ⟨((563887148220797/4398046511104), (-883211697737943/8796093022208)), (928721/1099511627776), by norm_num⟩
  | 5 => ⟨((109204192509525/17179869184), (-221170515463197/8589934592)), (26540831/68719476736), by norm_num⟩
  | 6 => ⟨((-652775724956341/1048576), (-343231186378629/1048576)), (52006289/2097152), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((1367098809/67108864), (2659887729/268435456)), (13/1073741824), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((90112/1098073), (-252672/1098073)), 0, by norm_num⟩
  | 1 => ⟨((27861483520/1205764313329), (22768779264/1205764313329)), 0, by norm_num⟩
  | 2 => ⟨((-4131843498573824/1324017236830115017), (2494038263463936/1324017236830115017)), 0, by norm_num⟩
  | 3 => ⟨((-389999103/4398046511104), (-15352140519/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((15154565653/281474976710656), (1083857375/140737488355328)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-108902655/35184372088832), (3309249295/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-9895730591/18014398509481984), (-10760224485/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 7 => ⟨((411007683/4503599627370496), (-2788063619/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 8 => ⟨((1630172441/2305843009213693952), (6967988909/576460752303423488)), (19/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-26189008831/18446744073709551616), (-3824333601/9223372036854775808)), (25/18446744073709551616), by norm_num⟩
  | 10 => ⟨((122161391/1152921504606846976), (-10797082781/73786976294838206464)), (17/73786976294838206464), by norm_num⟩
  | 11 => ⟨((3685720777/295147905179352825856), (5370170389/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-24610667789/9444732965739290427392), (6518497711/9444732965739290427392)), (7/1180591620717411303424), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (987/256)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (987/256)))⁻¹=value ((90112/1098073), (-252672/1098073)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((90112/1098073), (-252672/1098073))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((155648/1343833), (-252672/1343833)), 0, by norm_num⟩
  | 1 => ⟨((19808419840/1805887131889), (39327891456/1805887131889)), 0, by norm_num⟩
  | 2 => ⟨((-6510098960613376/2426810722107790537), (-558137295765504/2426810722107790537)), 0, by norm_num⟩
  | 3 => ⟨((3113371141/17592186044416), (-16809279117/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((6872503377/562949953421312), (17153850301/562949953421312)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-8042649747/2251799813685248), (-1389269825/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((4770985481/18014398509481984), (-675647691/2251799813685248)), (5/36028797018963968), by norm_num⟩
  | 7 => ⟨((3709649511/288230376151711744), (6092424097/144115188075855872)), (13/576460752303423488), by norm_num⟩
  | 8 => ⟨((-10882809069/2305843009213693952), (-5710368419/4611686018427387904)), (17/4611686018427387904), by norm_num⟩
  | 9 => ⟨((3594661793/9223372036854775808), (-13724189963/36893488147419103232)), (11/18446744073709551616), by norm_num⟩
  | 10 => ⟨((3660308539/295147905179352825856), (17172444069/295147905179352825856)), (7/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-7305543905/1180591620717411303424), (-5203024767/2361183241434822606848)), (35/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((10682414465/18889465931478580854784), (-8578364663/18889465931478580854784)), (11/4722366482869645213696), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (987/256)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (987/256)))⁻¹=value ((155648/1343833), (-252672/1343833)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((155648/1343833), (-252672/1343833))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-49817387008/1475626733809), (-62096670720/1475626733809)), 0, by norm_num⟩
  | 1 => ⟨((26691972795/2199023255552), (-6364692401/2199023255552)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-3853684895/8796093022208), (9296054845/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-18693470213/70368744177664), (-13895001921/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((11718313965/281474976710656), (-6409210401/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((1072879827/2251799813685248), (29252534011/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-14666716073/18014398509481984), (-5355042957/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 7 => ⟨((11297421101/144115188075855872), (-1458568917/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 8 => ⟨((1564122689/288230376151711744), (15363569923/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 9 => ⟨((-16689166209/9223372036854775808), (-196643055/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 10 => ⟨((6903251889/73786976294838206464), (-15090193799/73786976294838206464)), (11/36893488147419103232), by norm_num⟩
  | 11 => ⟨((11024213507/590295810358705651712), (6020548485/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-14975937511/4722366482869645213696), (2701920011/2361183241434822606848)), (39/4722366482869645213696), by norm_num⟩
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
  | 0 => ⟨((27/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((24576/191185), (-84224/573555)), 0, by norm_num⟩
  | 1 => ⟨((828932096/328965338025), (689963008/36551704225)), 0, by norm_num⟩
  | 2 => ⟨((-10817009352704/6988137572256625), (-194005178515456/188679714450928875)), 0, by norm_num⟩
  | 3 => ⟨((12313382203/70368744177664), (-6694170781/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-2182654229/281474976710656), (17907349277/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((-3014663499/4503599627370496), (-14335856381/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 6 => ⟨((11520801937/72057594037927936), (1914864249/36028797018963968)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((-8173310237/576460752303423488), (9595868569/1152921504606846976)), (9/1152921504606846976), by norm_num⟩
  | 8 => ⟨((2768705355/9223372036854775808), (-113560489/72057594037927936)), (11/9223372036854775808), by norm_num⟩
  | 9 => ⟨((14228832815/147573952589676412928), (18200628287/147573952589676412928)), (25/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-4501735845/295147905179352825856), (-1000683159/1180591620717411303424)), (29/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((9846640409/9444732965739290427392), (-10062424223/9444732965739290427392)), (33/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1695035541/151115727451828646838272), (21915329549/151115727451828646838272)), (37/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (987/256)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (987/256)))⁻¹=value ((24576/191185), (-84224/573555)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((24576/191185), (-84224/573555))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2967655434682368/282117697103273665), (-382443735482368/846353091309820995)), 0, by norm_num⟩
  | 1 => ⟨((8112454147/4398046511104), (-3186149629/1099511627776)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((6126922135/17592186044416), (11570743581/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-9416786287/70368744177664), (-432808195/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((12198816095/1125899906842624), (-1313662279/70368744177664)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((7608197825/4503599627370496), (12431572735/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-8278750535/18014398509481984), (125946337/4503599627370496)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((3699634393/144115188075855872), (-8280745931/144115188075855872)), (11/288230376151711744), by norm_num⟩
  | 8 => ⟨((3010995865/576460752303423488), (3743548551/576460752303423488)), (15/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-19394525951/18446744073709551616), (4175300649/18446744073709551616)), (21/18446744073709551616), by norm_num⟩
  | 10 => ⟨((4862740793/147573952589676412928), (-9722923757/73786976294838206464)), (29/147573952589676412928), by norm_num⟩
  | 11 => ⟨((7646200243/590295810358705651712), (12712951647/1180591620717411303424)), (5/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-17593571267/9444732965739290427392), (8233285237/9444732965739290427392)), (53/9444732965739290427392), by norm_num⟩
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
  | 0 => ⟨((35/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((40960/318367), (-36096/318367)), 0, by norm_num⟩
  | 1 => ⟨((-26771456/14479649527), (1478492160/101357546689)), 0, by norm_num⟩
  | 2 => ⟨((-22845870571520/32268898066736863), (-33661718102016/32268898066736863)), 0, by norm_num⟩
  | 3 => ⟨((7366170015/70368744177664), (118614203/4398046511104)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-9303031939/1125899906842624), (2363992107/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((1321687675/4503599627370496), (-13304405903/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((6626076869/288230376151711744), (4622206567/72057594037927936)), (9/288230376151711744), by norm_num⟩
  | 7 => ⟨((-11794900621/2305843009213693952), (-3254906779/1152921504606846976)), (5/1152921504606846976), by norm_num⟩
  | 8 => ⟨((18044517419/36893488147419103232), (-1999035949/18446744073709551616)), (21/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-1868249631/73786976294838206464), (5120479985/147573952589676412928)), (21/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-798621359/2361183241434822606848), (-17318756657/4722366482869645213696)), (21/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((17352574909/75557863725914323419136), (16376626963/75557863725914323419136)), (83/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-4089281223/151115727451828646838272), (-1116399539/1208925819614629174706176)), (81/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (987/256)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (987/256)))⁻¹=value ((40960/318367), (-36096/318367)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((40960/318367), (-36096/318367))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6177487353/4398046511104), (9979315621/8796093022208)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-2293737965/35184372088832), (-6461256247/8796093022208)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((11625949589/70368744177664), (6241031767/70368744177664)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-18701950329/562949953421312), (5189648595/281474976710656)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((1662949029/4503599627370496), (-15086059729/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((7983560157/9007199254740992), (11087953477/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-5327405129/36028797018963968), (9562753109/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((2926626935/1152921504606846976), (-3308014245/144115188075855872)), (19/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1467806097/576460752303423488), (8595193605/4611686018427387904)), (7/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-6992350813/18446744073709551616), (6374264451/36893488147419103232)), (5/9223372036854775808), by norm_num⟩
  | 10 => ⟨((573917551/147573952589676412928), (-31457917805/590295810358705651712)), (55/590295810358705651712), by norm_num⟩
  | 11 => ⟨((3340072583/590295810358705651712), (1052330201/295147905179352825856)), (19/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-6676815041/9444732965739290427392), (7834630291/18889465931478580854784)), (51/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((43/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((352256/2867545), (-252672/2867545)), 0, by norm_num⟩
  | 1 => ⟨((-30120574976/8222814327025), (89005228032/8222814327025)), 0, by norm_num⟩
  | 2 => ⟨((-4431370705/17592186044416), (-14534974687/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((14600804641/281474976710656), (11160344461/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-22215874821/4503599627370496), (-675375733/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((5577121711/18014398509481984), (-1874573675/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((-2838023539/288230376151711744), (7615830673/288230376151711744)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1289739269/2305843009213693952), (-18969877763/9223372036854775808)), (5/2305843009213693952), by norm_num⟩
  | 8 => ⟨((18442062567/147573952589676412928), (3751452381/36893488147419103232)), (35/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-28701555081/2361183241434822606848), (-1746702791/2361183241434822606848)), (15/590295810358705651712), by norm_num⟩
  | 10 => ⟨((14718705895/18889465931478580854784), (-4628902275/9444732965739290427392)), (13/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-3969338891/151115727451828646838272), (19473443815/302231454903657293676544)), (89/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-5925478735/4835703278458516698824704), (-24733405103/4835703278458516698824704)), (151/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (987/256)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (987/256)))⁻¹=value ((352256/2867545), (-252672/2867545)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((352256/2867545), (-252672/2867545))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2553571551/35184372088832), (9258135405/35184372088832)), (3/70368744177664), by norm_num⟩
  | 1 => ⟨((-11240524503/140737488355328), (-7307802773/70368744177664)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((5290496643/140737488355328), (-452076779/562949953421312)), (5/562949953421312), by norm_num⟩
  | 3 => ⟨((-5325406391/1125899906842624), (15532133611/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 4 => ⟨((-2514551141/4503599627370496), (-13398876177/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((18947471247/72057594037927936), (2315900961/36028797018963968)), (11/72057594037927936), by norm_num⟩
  | 6 => ⟨((-4510788433/144115188075855872), (4152959075/144115188075855872)), (9/288230376151711744), by norm_num⟩
  | 7 => ⟨((-4878536093/4611686018427387904), (-28557164203/4611686018427387904)), (27/4611686018427387904), by norm_num⟩
  | 8 => ⟨((15030498209/18446744073709551616), (6241020779/18446744073709551616)), (21/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-14210219945/147573952589676412928), (10292099277/147573952589676412928)), (15/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-812420223/590295810358705651712), (-18199016029/1180591620717411303424)), (21/590295810358705651712), by norm_num⟩
  | 11 => ⟨((8372415441/4722366482869645213696), (7797480625/9444732965739290427392)), (57/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-3694092607/18889465931478580854784), (5313342613/37778931862957161709568)), (39/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((51/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((139264/1212531), (-84224/1212531)), 0, by norm_num⟩
  | 1 => ⟨((-683376640/163359047329), (11729371136/1470231425961)), 0, by norm_num⟩
  | 2 => ⟨((-65683337510912/1782701181151917291), (-1075744784515072/1782701181151917291)), 0, by norm_num⟩
  | 3 => ⟨((1623659733/70368744177664), (2348474043/70368744177664)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-2796894937/1125899906842624), (-10044801653/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((26140808517/144115188075855872), (-801045377/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((-5559617979/576460752303423488), (8735151811/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((5362666029/18446744073709551616), (-7102494571/9223372036854775808)), (7/18446744073709551616), by norm_num⟩
  | 8 => ⟨((2966190117/295147905179352825856), (16031978013/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-11634248141/4722366482869645213696), (-13082406897/4722366482869645213696)), (17/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((4489921613/18889465931478580854784), (5555489459/75557863725914323419136)), (13/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-612158229/37778931862957161709568), (4875467581/1208925819614629174706176)), (39/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((15289802463/19342813113834066795298816), (-15365191567/19342813113834066795298816)), (29/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (987/256)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (987/256)))⁻¹=value ((139264/1212531), (-84224/1212531)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((139264/1212531), (-84224/1212531))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1399177779/140737488355328), (19851328889/562949953421312)), (3/281474976710656), by norm_num⟩
  | 1 => ⟨((-2558951073/140737488355328), (-2268569651/281474976710656)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((3144525557/562949953421312), (-6467217033/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 3 => ⟨((-5136939777/18014398509481984), (3331985251/2251799813685248)), (7/9007199254740992), by norm_num⟩
  | 4 => ⟨((-911852317/4503599627370496), (-8176696755/36028797018963968)), (13/72057594037927936), by norm_num⟩
  | 5 => ⟨((31229810945/576460752303423488), (-2813736589/576460752303423488)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-10456635191/2305843009213693952), (17629811543/2305843009213693952)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-10270165307/18446744073709551616), (-2846109835/2305843009213693952)), (31/18446744073709551616), by norm_num⟩
  | 8 => ⟨((28323077637/147573952589676412928), (4989010231/147573952589676412928)), (47/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-339622249/18446744073709551616), (11465297509/590295810358705651712)), (35/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-31216213/36893488147419103232), (-4049100119/1180591620717411303424)), (49/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((31631063/73786976294838206464), (5260518595/37778931862957161709568)), (17/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-6368911693/151115727451828646838272), (11070579849/302231454903657293676544)), (93/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((59/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((483328/4538713), (-252672/4538713)), 0, by norm_num⟩
  | 1 => ⟨((-84881408000/20599915696369), (122123452416/20599915696369)), 0, by norm_num⟩
  | 2 => ⟨((3826516473/70368744177664), (-30283144167/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((2556777681/281474976710656), (13751515087/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-10480763699/9007199254740992), (-4718906019/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((26264070543/288230376151711744), (1686260657/72057594037927936)), (11/288230376151711744), by norm_num⟩
  | 6 => ⟨((-12689451039/2305843009213693952), (5950809877/4611686018427387904)), (15/4611686018427387904), by norm_num⟩
  | 7 => ⟨((9485271221/36893488147419103232), (-8186224581/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-17323657/2305843009213693952), (22396812503/1180591620717411303424)), (15/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-2418424891/18889465931478580854784), (-5757638591/4722366482869645213696)), (5/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((12317269143/302231454903657293676544), (2317891333/37778931862957161709568)), (53/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-18751766805/4835703278458516698824704), (-5155809789/2417851639229258349412352)), (35/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((20567436607/77371252455336267181195264), (54166907/9671406556917033397649408)), (23/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (987/256)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (987/256)))⁻¹=value ((483328/4538713), (-252672/4538713)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((483328/4538713), (-252672/4538713))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6804503535/2251799813685248), (14419190459/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2966685763/1125899906842624), (38053345/562949953421312)), (13/9007199254740992), by norm_num⟩
  | 2 => ⟨((2582193057/4503599627370496), (-12497470961/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 3 => ⟨((1469648453/36028797018963968), (4077495003/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((-6149093205/144115188075855872), (-6863492973/288230376151711744)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((9721504731/1152921504606846976), (-7967849471/2305843009213693952)), (11/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-945526637/2305843009213693952), (13699896775/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-2721145597/18446744073709551616), (-14089482653/73786976294838206464)), (15/36893488147419103232), by norm_num⟩
  | 8 => ⟨((2618667545/73786976294838206464), (-302071563/295147905179352825856)), (45/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-6470717903/2361183241434822606848), (9765034163/2361183241434822606848)), (17/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-9453728763/37778931862957161709568), (-23219379159/37778931862957161709568)), (97/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((25337231057/302231454903657293676544), (5054205131/302231454903657293676544)), (135/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-557478839/75557863725914323419136), (2324182543/302231454903657293676544)), (47/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((67/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((548864/5570905), (-252672/5570905)), 0, by norm_num⟩
  | 1 => ⟨((-118704275456/31034982519025), (138682564608/31034982519025)), 0, by norm_num⟩
  | 2 => ⟨((6127764817/70368744177664), (-21594016083/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((3005463167/1125899906842624), (9621770707/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-4675645793/9007199254740992), (-14076981353/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((6239163179/144115188075855872), (7702215343/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-25259919595/9223372036854775808), (-385770371/1152921504606846976)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((10514663221/73786976294838206464), (-3366484011/73786976294838206464)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1766500727/295147905179352825856), (12937223997/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((6444446607/37778931862957161709568), (-7662337581/18889465931478580854784)), (19/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((240529379/302231454903657293676544), (3604259531/151115727451828646838272)), (11/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-5610316731/9671406556917033397649408), (-22377529351/19342813113834066795298816)), (51/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((8481765071/154742504910672534362390528), (1695789171/38685626227668133590597632)), (59/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (987/256)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (987/256)))⁻¹=value ((548864/5570905), (-252672/5570905)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((548864/5570905), (-252672/5570905))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((15958369059/36028797018963968), (6427048413/36028797018963968)), (3/9007199254740992), by norm_num⟩
  | 1 => ⟨((-10174633789/36028797018963968), (4591029551/36028797018963968)), (17/72057594037927936), by norm_num⟩
  | 2 => ⟨((1298692637/36028797018963968), (-15425683857/144115188075855872)), (13/144115188075855872), by norm_num⟩
  | 3 => ⟨((2152595849/144115188075855872), (956224953/36028797018963968)), (17/576460752303423488), by norm_num⟩
  | 4 => ⟨((-15268142947/2305843009213693952), (-3181050063/2305843009213693952)), (9/1152921504606846976), by norm_num⟩
  | 5 => ⟨((19027807697/18446744073709551616), (-14851309071/18446744073709551616)), (17/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-103061883/18446744073709551616), (16822829829/73786976294838206464)), (31/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-16580958825/590295810358705651712), (-13860276053/590295810358705651712)), (49/590295810358705651712), by norm_num⟩
  | 8 => ⟨((25341787337/4722366482869645213696), (-2811731937/2361183241434822606848)), (37/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-6040338687/18889465931478580854784), (6725703767/9444732965739290427392)), (57/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-3999051481/75557863725914323419136), (-6916221537/75557863725914323419136)), (41/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((8281847185/604462909807314587353088), (697658913/604462909807314587353088)), (57/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-5218932499/4835703278458516698824704), (6509578053/4835703278458516698824704)), (159/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((75/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((204800/2244723), (-84224/2244723)), 0, by norm_num⟩
  | 1 => ⟨((-5808226304/1679593782243), (17249075200/5038781346729)), 0, by norm_num⟩
  | 2 => ⟨((1057894065766400/11310668380973561067), (-2500093378822144/11310668380973561067)), 0, by norm_num⟩
  | 3 => ⟨((-270012155/2251799813685248), (3332110273/281474976710656)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-3902220017/18014398509481984), (-9768815083/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((11560933557/576460752303423488), (5958838575/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-375484373/288230376151711744), (-5228376819/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 7 => ⟨((646210957/9223372036854775808), (104740061/73786976294838206464)), (9/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-15218963357/4722366482869645213696), (5901285939/4722366482869645213696)), (5/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((9336791359/75557863725914323419136), (-8875519447/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-64854501/18889465931478580854784), (9280747061/1208925819614629174706176)), (13/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((975076569/77371252455336267181195264), (-32079283541/77371252455336267181195264)), (55/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((8917447349/1237940039285380274899124224), (23707021733/1237940039285380274899124224)), (29/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (987/256)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (987/256)))⁻¹=value ((204800/2244723), (-84224/2244723)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((204800/2244723), (-84224/2244723))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13577036307/288230376151711744), (-198283071/576460752303423488)), (13/288230376151711744), by norm_num⟩
  | 1 => ⟨((-13331564283/576460752303423488), (13328538009/576460752303423488)), (5/144115188075855872), by norm_num⟩
  | 2 => ⟨((-244902139/2305843009213693952), (-29069205887/2305843009213693952)), (1/72057594037927936), by norm_num⟩
  | 3 => ⟨((11990112137/4611686018427387904), (11225439703/4611686018427387904)), (11/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-30258294041/36893488147419103232), (2225210377/36893488147419103232)), (47/36893488147419103232), by norm_num⟩
  | 5 => ⟨((14784644649/147573952589676412928), (-19228013733/147573952589676412928)), (45/147573952589676412928), by norm_num⟩
  | 6 => ⟨((3493879561/590295810358705651712), (4255149937/147573952589676412928)), (21/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-20092253775/4722366482869645213696), (-10826618759/4722366482869645213696)), (69/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((6441547381/9444732965739290427392), (-5387838639/18889465931478580854784)), (53/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-4264102993/151115727451828646838272), (15530957937/151115727451828646838272)), (81/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-1345569465/151115727451828646838272), (-7001651635/604462909807314587353088)), (59/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((9269315579/4835703278458516698824704), (-114649531/2417851639229258349412352)), (83/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-5203657991/38685626227668133590597632), (15585357107/77371252455336267181195264)), (29/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((83/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((679936/8028505), (-252672/8028505)), 0, by norm_num⟩
  | 1 => ⟨((-199234912256/64456892535025), (171800788992/64456892535025)), 0, by norm_num⟩
  | 2 => ⟨((3129508051/35184372088832), (-5682430861/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-2758467299/2251799813685248), (18551611761/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-5603816153/72057594037927936), (-6631818075/18014398509481984)), (7/72057594037927936), by norm_num⟩
  | 5 => ⟨((10475609381/1152921504606846976), (4140476959/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((-11267327421/18446744073709551616), (-1072944987/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1224373253/36893488147419103232), (2978719677/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-29545137683/18889465931478580854784), (1791934977/18889465931478580854784)), (15/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2445789215/37778931862957161709568), (-2163199781/75557863725914323419136)), (29/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5539024277/2417851639229258349412352), (5394383759/2417851639229258349412352)), (7/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((4789279753/77371252455336267181195264), (-20197601651/154742504910672534362390528)), (53/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-1404434855/2475880078570760549798248448), (1005997397/154742504910672534362390528)), (25/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (987/256)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (987/256)))⁻¹=value ((679936/8028505), (-252672/8028505)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((679936/8028505), (-252672/8028505))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4586889075/1152921504606846976), (-3485527447/2305843009213693952)), (25/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-99122953/72057594037927936), (12970835679/4611686018427387904)), (5/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-7226727957/18446744073709551616), (-22229676593/18446744073709551616)), (17/9223372036854775808), by norm_num⟩
  | 3 => ⟨((12261490133/36893488147419103232), (3120935045/18446744073709551616)), (25/36893488147419103232), by norm_num⟩
  | 4 => ⟨((-3109986509/36893488147419103232), (4277486701/147573952589676412928)), (27/147573952589676412928), by norm_num⟩
  | 5 => ⟨((4425737779/590295810358705651712), (-19764881357/1180591620717411303424)), (27/590295810358705651712), by norm_num⟩
  | 6 => ⟨((6397347727/4722366482869645213696), (14557087851/4722366482869645213696)), (25/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-5084634771/9444732965739290427392), (-6402573457/37778931862957161709568)), (21/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((5610004823/75557863725914323419136), (-7089730965/151115727451828646838272)), (33/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-1887110905/1208925819614629174706176), (15410340673/1208925819614629174706176)), (101/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-6059795731/4835703278458516698824704), (-1529410635/1208925819614629174706176)), (149/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((18090778351/77371252455336267181195264), (-2359139785/77371252455336267181195264)), (53/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-8958646123/618970019642690137449562112), (508009627/19342813113834066795298816)), (297/618970019642690137449562112), by norm_num⟩
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
  | 0 => ⟨((91/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((106496/1350559), (-36096/1350559)), 0, by norm_num⟩
  | 1 => ⟨((-5019238400/1824009612481), (3844079616/1824009612481)), 0, by norm_num⟩
  | 2 => ⟨((197886457413632/2463432598222726879), (-295276766035968/2463432598222726879)), 0, by norm_num⟩
  | 3 => ⟨((-7049663975/4503599627370496), (1632359249/281474976710656)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((-1137219279/72057594037927936), (-2247884291/9007199254740992)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((2281207575/576460752303423488), (22202082741/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-10503291193/36893488147419103232), (-12054641843/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((18406397361/1180591620717411303424), (10717272937/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-27805474649/37778931862957161709568), (-2825196853/18889465931478580854784)), (7/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((4687138347/151115727451828646838272), (-1190387343/302231454903657293676544)), (13/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-11318036449/9671406556917033397649408), (11021104761/19342813113834066795298816)), (23/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((11922964769/309485009821345068724781056), (-5896151919/154742504910672534362390528)), (21/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-9999925147/9903520314283042199192993792), (19976374533/9903520314283042199192993792)), (37/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (987/256)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (987/256)))⁻¹=value ((106496/1350559), (-36096/1350559)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((106496/1350559), (-36096/1350559))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5041806121/18446744073709551616), (-8320482729/36893488147419103232)), (11/18446744073709551616), by norm_num⟩
  | 1 => ⟨((-3029819819/73786976294838206464), (20003097075/73786976294838206464)), (37/73786976294838206464), by norm_num⟩
  | 2 => ⟨((-9607524229/147573952589676412928), (-7068087929/73786976294838206464)), (33/147573952589676412928), by norm_num⟩
  | 3 => ⟨((20409729411/590295810358705651712), (4347533997/590295810358705651712)), (49/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-8658427951/1180591620717411303424), (5560849055/1180591620717411303424)), (55/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((1747114643/4722366482869645213696), (-17040381441/9444732965739290427392)), (57/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((7507923035/37778931862957161709568), (10689310159/37778931862957161709568)), (27/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-17709898821/302231454903657293676544), (-2259153127/302231454903657293676544)), (91/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((16951442031/2417851639229258349412352), (-14923502237/2417851639229258349412352)), (145/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((228861593/9671406556917033397649408), (13384383397/9671406556917033397649408)), (223/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-11764495361/77371252455336267181195264), (-4662073407/38685626227668133590597632)), (167/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((15615211611/618970019642690137449562112), (-1836505117/309485009821345068724781056)), (239/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-3354049933/2475880078570760549798248448), (1874784339/618970019642690137449562112)), (337/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((99/8), (987/256)), 0, by norm_num⟩
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
  | 0 => ⟨((90112/1223377), (-84224/3670131)), 0, by norm_num⟩
  | 1 => ⟨((-32993935360/13469861557161), (7589593088/4489953852387)), 0, by norm_num⟩
  | 2 => ⟨((9966507443/140737488355328), (-6358519529/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-3538240697/2251799813685248), (4661732885/1125899906842624)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((746585911/72057594037927936), (-24574366217/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((3631681425/2305843009213693952), (14754997615/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-9697742773/73786976294838206464), (-16055807485/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1082776969/147573952589676412928), (7680772343/1180591620717411303424)), (17/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-13028915327/37778931862957161709568), (-5871497503/37778931862957161709568)), (7/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((17510899135/1208925819614629174706176), (1067928713/604462909807314587353088)), (23/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-21421434317/38685626227668133590597632), (3912400143/38685626227668133590597632)), (9/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((11904679975/618970019642690137449562112), (-779770937/77371252455336267181195264)), (29/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-5869785349/9903520314283042199192993792), (11723008315/19807040628566084398385987584)), (23/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (987/256)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (987/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (987/256)))⁻¹=value ((90112/1223377), (-84224/3670131)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((90112/1223377), (-84224/3670131))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4414401691/295147905179352825856), (-13508436299/590295810358705651712)), (35/590295810358705651712), by norm_num⟩
  | 1 => ⟨((3433592639/1180591620717411303424), (12942217389/590295810358705651712)), (61/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((-17360185089/2361183241434822606848), (-14960129083/2361183241434822606848)), (57/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((28893952513/9444732965739290427392), (-963145767/9444732965739290427392)), (43/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((-10268625507/18889465931478580854784), (1308354499/2361183241434822606848)), (51/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-74059615/151115727451828646838272), (-25392154545/151115727451828646838272)), (53/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((13949538329/604462909807314587353088), (13578283841/604462909807314587353088)), (51/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-3382205193/604462909807314587353088), (1120024729/4835703278458516698824704)), (11/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((11183793463/19342813113834066795298816), (-13312875439/19342813113834066795298816)), (71/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((3111066031/154742504910672534362390528), (20638950969/154742504910672534362390528)), (221/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((-20099623027/1237940039285380274899124224), (-3116135039/309485009821345068724781056)), (333/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((24120619181/9903520314283042199192993792), (-8234852251/9903520314283042199192993792)), (241/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-273423629/2475880078570760549798248448), (6194857467/19807040628566084398385987584)), (683/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18473658417/1099511627776), (10280947007/1099511627776)), (1095/1099511627776), by norm_num⟩
  | 1 => ⟨((-9797999209/549755813888), (-21028439/4294967296)), (1163/549755813888), by norm_num⟩
  | 2 => ⟨((-9446264041/2199023255552), (-15595681395/2199023255552)), (2637/1099511627776), by norm_num⟩
  | 3 => ⟨((1748853989/4398046511104), (-19701202325/8796093022208)), (16319/8796093022208), by norm_num⟩
  | 4 => ⟨((10777565755/35184372088832), (-10202139227/35184372088832)), (38519/35184372088832), by norm_num⟩
  | 5 => ⟨((7742563611/140737488355328), (-1212444011/70368744177664)), (147769/281474976710656), by norm_num⟩
  | 6 => ⟨((8297251893/1125899906842624), (-808447005/1125899906842624)), (479891/2251799813685248), by norm_num⟩
  | 7 => ⟨((18612545073/18014398509481984), (2999918615/18014398509481984)), (1357373/18014398509481984), by norm_num⟩
  | 8 => ⟨((14571006157/144115188075855872), (9646071653/144115188075855872)), (213371/9007199254740992), by norm_num⟩
  | 9 => ⟨((1833946919/288230376151711744), (17870089089/2305843009213693952)), (7758863/1152921504606846976), by norm_num⟩
  | 10 => ⟨((6204526359/9223372036854775808), (6264054553/9223372036854775808)), (16134319/9223372036854775808), by norm_num⟩
  | 11 => ⟨((3977046523/73786976294838206464), (15761524661/147573952589676412928)), (3877217/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-4026646401/2361183241434822606848), (2611559229/295147905179352825856)), (55591175/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18473658417/1099511627776), (10280947007/1099511627776)), (137/137438953472), by norm_num⟩
  | 1 => ⟨((-9797999209/549755813888), (-21028439/4294967296)), (2327/1099511627776), by norm_num⟩
  | 2 => ⟨((-9446264041/2199023255552), (-15595681395/2199023255552)), (5275/2199023255552), by norm_num⟩
  | 3 => ⟨((1748853989/4398046511104), (-19701202325/8796093022208)), (255/137438953472), by norm_num⟩
  | 4 => ⟨((10777565755/35184372088832), (-10202139227/35184372088832)), (38521/35184372088832), by norm_num⟩
  | 5 => ⟨((7742563611/140737488355328), (-1212444011/70368744177664)), (147781/281474976710656), by norm_num⟩
  | 6 => ⟨((8297251893/1125899906842624), (-808447005/1125899906842624)), (239991/1125899906842624), by norm_num⟩
  | 7 => ⟨((18612545073/18014398509481984), (2999918615/18014398509481984)), (679047/9007199254740992), by norm_num⟩
  | 8 => ⟨((14571006157/144115188075855872), (9646071653/144115188075855872)), (3419701/144115188075855872), by norm_num⟩
  | 9 => ⟨((1833946919/288230376151711744), (17870089089/2305843009213693952)), (1951245/288230376151711744), by norm_num⟩
  | 10 => ⟨((6204526359/9223372036854775808), (6264054553/9223372036854775808)), (8251627/4611686018427387904), by norm_num⟩
  | 11 => ⟨((3977046523/73786976294838206464), (15761524661/147573952589676412928)), (67938431/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-4026646401/2361183241434822606848), (2611559229/295147905179352825856)), (158406015/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile017Gamma
