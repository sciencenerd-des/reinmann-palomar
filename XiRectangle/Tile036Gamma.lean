/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile036Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨36,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8601/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8601/640))
  have he : value ((7/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((23/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((215/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((22016000/369817201), (-11009280/369817201)), 0, by norm_num⟩
  | 1 => ⟨((-181750004940800/136764762155474401), (242380308480000/136764762155474401)), 0, by norm_num⟩
  | 2 => ⟨((115909929/8796093022208), (-1276020813/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((386972781/562949953421312), (662923063/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1000113739/18014398509481984), (-1078566883/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((183294605/72057594037927936), (275491703/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1659165347/18446744073709551616), (43406119/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 7 => ⟨((748839237/295147905179352825856), (-477830285/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-485683293/9444732965739290427392), (811821293/9444732965739290427392)), (3/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((9492449/37778931862957161709568), (-1004607937/302231454903657293676544)), (9/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((406173601/9671406556917033397649408), (993073919/9671406556917033397649408)), (27/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-214974823/77371252455336267181195264), (-376225583/154742504910672534362390528)), (5/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((588733857/4951760157141521099596496896), (307139539/9903520314283042199192993792)), (29/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((215/16), (8601/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((215/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((215/16), (8601/1280)))⁻¹=value ((22016000/369817201), (-11009280/369817201)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((22016000/369817201), (-11009280/369817201))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1454729227/536870912), (248943885/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((11008000/369817201), (-5504640/369817201)), 0, by norm_num⟩
  | 2 => ⟨((-45437501235200/136764762155474401), (60595077120000/136764762155474401)), 0, by norm_num⟩
  | 3 => ⟨((38636643/17592186044416), (-425340271/35184372088832)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((386972781/4503599627370496), (662923063/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-800090991/144115188075855872), (-431426753/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((977571227/4611686018427387904), (367322271/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-237023621/36893488147419103232), (198427973/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((748839237/4722366482869645213696), (-477830285/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-431718483/151115727451828646838272), (721618927/151115727451828646838272)), (3/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((121503347/9671406556917033397649408), (-1607372699/9671406556917033397649408)), (15/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((590797965/309485009821345068724781056), (1444471155/309485009821345068724781056)), (5/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-573266195/4951760157141521099596496896), (-501634111/4951760157141521099596496896)), (7/1237940039285380274899124224), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-6959/276736), (183/20480)), 0, by norm_num⟩
  | 45 => ⟨((91801946273/4080638361600), (-723033/60293120)), 0, by norm_num⟩
  | 44 => ⟨((-9787652660945/459643105050624), (6738261877853/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((752192571/34359738368), (-184917721/17179869184)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-195809325/8589934592), (93782575/8589934592)), (1/17179869184), by norm_num⟩
  | 41 => ⟨((201484753/8589934592), (-194508091/17179869184)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-412347115/17179869184), (200387073/17179869184)), (1/17179869184), by norm_num⟩
  | 39 => ⟨((211196367/8589934592), (-102633475/8589934592)), (1/17179869184), by norm_num⟩
  | 38 => ⟨((-867089103/34359738368), (420534717/34359738368)), (1/17179869184), by norm_num⟩
  | 37 => ⟨((55681191/2147483648), (-107875821/8589934592)), (1/17179869184), by norm_num⟩
  | 36 => ⟨((-915901491/34359738368), (443259451/34359738368)), (1/17179869184), by norm_num⟩
  | 35 => ⟨((942238175/34359738368), (-455642565/34359738368)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-970129345/34359738368), (468686433/34359738368)), (3/34359738368), by norm_num⟩
  | 33 => ⟨((249935475/8589934592), (-482488965/34359738368)), (3/34359738368), by norm_num⟩
  | 32 => ⟨((-257806377/8589934592), (124283983/8589934592)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((266188335/8589934592), (-64087991/4294967296)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-1100530885/34359738368), (529277947/34359738368)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((142349279/4294967296), (-546957901/34359738368)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-1179812233/34359738368), (565858941/34359738368)), (1/17179869184), by norm_num⟩
  | 27 => ⟨((305973257/8589934592), (-586112419/34359738368)), (1/17179869184), by norm_num⟩
  | 26 => ⟨((-158924059/4294967296), (607868783/34359738368)), (1/17179869184), by norm_num⟩
  | 25 => ⟨((1322723905/34359738368), (-631301575/34359738368)), (1/17179869184), by norm_num⟩
  | 24 => ⟨((-1378370099/34359738368), (656612181/34359738368)), (1/17179869184), by norm_num⟩
  | 23 => ⟨((1438898375/34359738368), (-171008901/8589934592)), (1/17179869184), by norm_num⟩
  | 22 => ⟨((-188122493/4294967296), (178461935/8589934592)), (1/17179869184), by norm_num⟩
  | 21 => ⟨((197176853/4294967296), (-373187331/17179869184)), (1/17179869184), by norm_num⟩
  | 20 => ⟨((-828582135/17179869184), (195501145/8589934592)), (1/17179869184), by norm_num⟩
  | 19 => ⟨((436348371/8589934592), (-205300841/8589934592)), (1/8589934592), by norm_num⟩
  | 18 => ⟨((-921764337/17179869184), (216133745/8589934592)), (1/8589934592), by norm_num⟩
  | 17 => ⟨((488333589/8589934592), (-456344357/17179869184)), (1/8589934592), by norm_num⟩
  | 16 => ⟨((-259627479/4294967296), (241629001/8589934592)), (1/8589934592), by norm_num⟩
  | 15 => ⟨((1108694263/17179869184), (-513540529/17179869184)), (1/8589934592), by norm_num⟩
  | 14 => ⟨((-297256463/4294967296), (547865835/17179869184)), (1/8589934592), by norm_num⟩
  | 13 => ⟨((10014615/134217728), (-587100161/17179869184)), (1/8589934592), by norm_num⟩
  | 12 => ⟨((-1390390505/17179869184), (158093977/4294967296)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((189863333/2147483648), (-85650279/2147483648)), (1/8589934592), by norm_num⟩
  | 10 => ⟨((-836742225/8589934592), (93454465/2147483648)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((232863531/2147483648), (-411276487/8589934592)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((-262548987/2147483648), (457051943/8589934592)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((300845133/2147483648), (-64281407/1073741824)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-1408414217/8589934592), (587745121/8589934592)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((848358763/4294967296), (-171405941/2147483648)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((-1065640835/4294967296), (102797323/1073741824)), (1/4294967296), by norm_num⟩
  | 3 => ⟨((1429637349/4294967296), (-256696233/2147483648)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-1080419605/2147483648), (341314407/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((544294387/536870912), (-63551027/268435456)), (1/536870912), by norm_num⟩
  | 0 => ⟨((-33793009/536870912), (995775539/2147483648)), (3/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-41/256), (8601/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-41/256), (8601/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-41/256), (8601/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((1454729227/536870912), (248943885/536870912)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((215/16), (8601/1280))) (z:=((-41/256), (8601/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((1454729227/536870912), (248943885/536870912))) (r:=(1/268435456)) (by norm_num) ?_ hs
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
  | 0 => ⟨((207/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((535867911/16777216), (406119063/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((246952451/134217728), (32116885/134217728)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1040455687769600/136764762155474401), (-539225177888160/136764762155474401)), 0, by norm_num⟩
  | 3 => ⟨((-248357519/4398046511104), (702701237/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((260721545/1125899906842624), (-1867091849/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((409589599/36028797018963968), (1168533591/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-163897599/288230376151711744), (-77643869/144115188075855872)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((1354247881/73786976294838206464), (394993387/73786976294838206464)), (25/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-283826073/590295810358705651712), (218671563/2361183241434822606848)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((386782247/37778931862957161709568), (-605142765/75557863725914323419136)), (183/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-180281353/1208925819614629174706176), (778216727/2417851639229258349412352)), (61/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-59333421/154742504910672534362390528), (-765058057/77371252455336267181195264)), (317/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((680498407/4951760157141521099596496896), (1213797817/4951760157141521099596496896)), (871/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215/16), (-8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((310424071/16777216), (73346009/4194304)), (5/33554432), by norm_num⟩
  | 1 => ⟨((179843587/134217728), (32116885/134217728)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1040455687769600/136764762155474401), (-539225177888160/136764762155474401)), 0, by norm_num⟩
  | 3 => ⟨((-248357519/4398046511104), (702701237/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((260721545/1125899906842624), (-1867091849/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((409589599/36028797018963968), (1168533591/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-163897599/288230376151711744), (-77643869/144115188075855872)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((1354247881/73786976294838206464), (394993387/73786976294838206464)), (25/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-283826073/590295810358705651712), (218671563/2361183241434822606848)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((386782247/37778931862957161709568), (-605142765/75557863725914323419136)), (183/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-180281353/1208925819614629174706176), (778216727/2417851639229258349412352)), (61/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-59333421/154742504910672534362390528), (-765058057/77371252455336267181195264)), (317/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((680498407/4951760157141521099596496896), (1213797817/4951760157141521099596496896)), (871/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((986702737/536870912), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((986702737/1073741824), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((651682603/33554432), (73346009/4194304)), (3/16777216), by norm_num⟩
  | 1 => ⟨((179843587/134217728), (32116885/134217728)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1040455687769600/136764762155474401), (-539225177888160/136764762155474401)), 0, by norm_num⟩
  | 3 => ⟨((-248357519/4398046511104), (702701237/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((260721545/1125899906842624), (-1867091849/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((409589599/36028797018963968), (1168533591/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-163897599/288230376151711744), (-77643869/144115188075855872)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((1354247881/73786976294838206464), (394993387/73786976294838206464)), (25/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-283826073/590295810358705651712), (218671563/2361183241434822606848)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((386782247/37778931862957161709568), (-605142765/75557863725914323419136)), (183/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-180281353/1208925819614629174706176), (778216727/2417851639229258349412352)), (61/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-59333421/154742504910672534362390528), (-765058057/77371252455336267181195264)), (317/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((680498407/4951760157141521099596496896), (1213797817/4951760157141521099596496896)), (871/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((363500009881600/136764762155474401), (-484760616960000/136764762155474401)), 0, by norm_num⟩
  | 1 => ⟨((-115909929/2199023255552), (1276020813/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-145114793/35184372088832), (-497192297/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((1000113739/2251799813685248), (1078566883/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-916473025/36028797018963968), (-344364629/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((622187005/576460752303423488), (-130218357/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-163808583/4611686018427387904), (104525375/4611686018427387904)), (5/18446744073709551616), by norm_num⟩
  | 7 => ⟨((121420823/147573952589676412928), (-811821293/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-10679005/2361183241434822606848), (1130183929/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-507717001/604462909807314587353088), (-620671199/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((591180763/9671406556917033397649408), (16165943/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-883100785/309485009821345068724781056), (-115177327/154742504910672534362390528)), (3/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((32191469/309485009821345068724781056), (-54495937/2475880078570760549798248448)), (35/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((115909929/2199023255552), (-1276020813/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((145114793/17592186044416), (497192297/17592186044416)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((-93760663/70368744177664), (-404462581/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((916473025/9007199254740992), (344364629/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((-1555467513/288230376151711744), (162772947/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 5 => ⟨((491425749/2305843009213693952), (-313576125/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-424972881/73786976294838206464), (44396477/4611686018427387904)), (7/73786976294838206464), by norm_num⟩
  | 7 => ⟨((10679005/295147905179352825856), (-141272991/295147905179352825856)), (11/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((571181627/75557863725914323419136), (698255099/37778931862957161709568)), (17/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-369487977/604462909807314587353088), (-80829715/151115727451828646838272)), (7/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1214263579/38685626227668133590597632), (316737649/38685626227668133590597632)), (23/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-96574407/77371252455336267181195264), (326975623/1237940039285380274899124224)), (9/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((767709151/19807040628566084398385987584), (-611007859/19807040628566084398385987584)), (7/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-386972781/70368744177664), (-662923063/35184372088832)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((1000113739/562949953421312), (539283441/281474976710656)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((-916473025/4503599627370496), (-344364629/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 3 => ⟨((518489171/36028797018963968), (-54257649/36028797018963968)), (5/72057594037927936), by norm_num⟩
  | 4 => ⟨((-819042915/1152921504606846976), (522626875/1152921504606846976)), (5/1152921504606846976), by norm_num⟩
  | 5 => ⟨((424972881/18446744073709551616), (-44396477/1152921504606846976)), (7/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-99670713/590295810358705651712), (1318547917/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-380787751/9444732965739290427392), (-465503399/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((277115983/75557863725914323419136), (242489145/75557863725914323419136)), (19/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-252971579/1208925819614629174706176), (-263948041/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((354106159/38685626227668133590597632), (-149863827/77371252455336267181195264)), (27/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-383854575/1237940039285380274899124224), (611007859/2475880078570760549798248448)), (11/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((137569697/19807040628566084398385987584), (-1184578433/79228162514264337593543950336)), (35/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1000113739/1125899906842624), (-1078566883/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((916473025/4503599627370496), (86091157/1125899906842624)), (3/4503599627370496), by norm_num⟩
  | 2 => ⟨((-194433439/9007199254740992), (81386473/36028797018963968)), (7/72057594037927936), by norm_num⟩
  | 3 => ⟨((819042915/576460752303423488), (-522626875/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((-531216101/9223372036854775808), (221982385/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149506069/295147905179352825856), (-1977821875/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 6 => ⟨((333189283/2361183241434822606848), (814630949/2361183241434822606848)), (5/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-1108463931/75557863725914323419136), (-242489145/18889465931478580854784)), (5/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((569186053/604462909807314587353088), (148470773/604462909807314587353088)), (9/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-1770530795/38685626227668133590597632), (23416223/2417851639229258349412352)), (1/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((527800041/309485009821345068724781056), (-420067903/309485009821345068724781056)), (7/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-412709091/9903520314283042199192993792), (888433825/9903520314283042199192993792)), (3/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-40081115/316912650057057350374175801344), (-695215949/158456325028528675187087900672)), (39/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-183294605/2251799813685248), (-275491703/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 1 => ⟨((622187005/36028797018963968), (-65109179/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 2 => ⟨((-982851497/576460752303423488), (627152249/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 3 => ⟨((26560805/288230376151711744), (-710343631/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-149506069/147573952589676412928), (1977821875/147573952589676412928)), (19/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-399827139/1180591620717411303424), (-488778569/590295810358705651712)), (13/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((775924753/18889465931478580854784), (339484803/9444732965739290427392)), (15/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-910697685/302231454903657293676544), (-59388309/75557863725914323419136)), (1/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((1593477715/9671406556917033397649408), (-337193611/9671406556917033397649408)), (15/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-527800041/77371252455336267181195264), (420067903/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((14186875/77371252455336267181195264), (-977277207/2475880078570760549798248448)), (13/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((24048669/39614081257132168796771975168), (1668518277/79228162514264337593543950336)), (23/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-297694491/633825300114114700748351602688), (-1109517317/1267650600228229401496703205376)), (39/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1659165347/288230376151711744), (43406119/72057594037927936)), (5/144115188075855872), by norm_num⟩
  | 1 => ⟨((1310468663/1152921504606846976), (-104525375/144115188075855872)), (11/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-26560805/288230376151711744), (710343631/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((99670713/73786976294838206464), (-1318547915/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 4 => ⟨((333189283/590295810358705651712), (203657737/147573952589676412928)), (11/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-48495297/590295810358705651712), (-678969605/9444732965739290427392)), (1/590295810358705651712), by norm_num⟩
  | 6 => ⟨((1062480633/151115727451828646838272), (138572721/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-1062318477/2417851639229258349412352), (224795741/2417851639229258349412352)), (23/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((791700061/38685626227668133590597632), (-630101855/38685626227668133590597632)), (23/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-189158333/309485009821345068724781056), (814397673/618970019642690137449562112)), (23/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-22044613/9903520314283042199192993792), (-1529475087/19807040628566084398385987584)), (11/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((297694491/158456325028528675187087900672), (277379329/79228162514264337593543950336)), (41/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-821694737/5070602400912917605986812821504), (-579929625/5070602400912917605986812821504)), (37/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-748839237/2305843009213693952), (477830285/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((485683291/9223372036854775808), (-811821293/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-85432039/73786976294838206464), (1130183927/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-380787751/590295810358705651712), (-931006797/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 4 => ⟨((1108463931/9444732965739290427392), (484978289/4722366482869645213696)), (25/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-227674421/18889465931478580854784), (-59388309/18889465931478580854784)), (19/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((1062318477/1208925819614629174706176), (-112397871/604462909807314587353088)), (25/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-452400035/9671406556917033397649408), (360058203/9671406556917033397649408)), (15/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((243203571/154742504910672534362390528), (-523541361/154742504910672534362390528)), (33/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((31492305/4951760157141521099596496896), (1092482205/4951760157141521099596496896)), (35/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-467805629/79228162514264337593543950336), (-435881803/39614081257132168796771975168)), (35/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((352154887/633825300114114700748351602688), (62135317/158456325028528675187087900672)), (17/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-1437082935/40564819207303340847894502572032), (-218510429/40564819207303340847894502572032)), (63/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-485683293/36893488147419103232), (811821293/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 1 => ⟨((85432039/147573952589676412928), (-141272991/18446744073709551616)), (17/147573952589676412928), by norm_num⟩
  | 2 => ⟨((571181627/1180591620717411303424), (1396510195/1180591620717411303424)), (27/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-554231965/4722366482869645213696), (-484978289/4722366482869645213696)), (29/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((1138372105/75557863725914323419136), (296941545/75557863725914323419136)), (27/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-1593477713/1208925819614629174706176), (84298403/302231454903657293676544)), (21/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((197925015/2417851639229258349412352), (-630101855/9671406556917033397649408)), (15/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-243203571/77371252455336267181195264), (523541361/77371252455336267181195264)), (19/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-35428843/2475880078570760549798248448), (-1229042481/2475880078570760549798248448)), (11/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((146189259/9903520314283042199192993792), (1089704507/39614081257132168796771975168)), (49/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-242106485/158456325028528675187087900672), (-683488487/633825300114114700748351602688)), (13/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((1077812201/10141204801825835211973625643008), (81941411/5070602400912917605986812821504)), (13/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-920575363/162259276829213363391578010288128), (297728791/162259276829213363391578010288128)), (51/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9492449/73786976294838206464), (1004607937/590295810358705651712)), (9/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-253858501/1180591620717411303424), (-1241342397/2361183241434822606848)), (7/590295810358705651712), by norm_num⟩
  | 2 => ⟨((369487977/4722366482869645213696), (323318859/4722366482869645213696)), (3/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-1011886315/75557863725914323419136), (-32993505/9444732965739290427392)), (7/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((221316349/151115727451828646838272), (-23416223/75557863725914323419136)), (27/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-65975005/604462909807314587353088), (420067903/4835703278458516698824704)), (45/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((378316665/77371252455336267181195264), (-101799709/9671406556917033397649408)), (17/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((31492305/1237940039285380274899124224), (1092482205/1237940039285380274899124224)), (23/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-146189259/4951760157141521099596496896), (-1089704507/19807040628566084398385987584)), (7/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((538014411/158456325028528675187087900672), (189857913/79228162514264337593543950336)), (33/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-164665753/633825300114114700748351602688), (-100150613/2535301200456458802993406410752)), (73/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((1227433817/81129638414606681695789005144064), (-396971721/81129638414606681695789005144064)), (19/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-107194629/162259276829213363391578010288128), (210604379/324518553658426726783156020576256)), (77/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((406173601/9444732965739290427392), (993073919/9444732965739290427392)), (27/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-591180763/18889465931478580854784), (-517310175/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((607131789/75557863725914323419136), (316737647/151115727451828646838272)), (41/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-1416424633/1208925819614629174706176), (299727655/1208925819614629174706176)), (13/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((65975005/604462909807314587353088), (-840135805/9671406556917033397649408)), (27/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((-453979999/77371252455336267181195264), (488638603/38685626227668133590597632)), (47/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((-11022307/309485009821345068724781056), (-1529475085/1237940039285380274899124224)), (37/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((467805629/9903520314283042199192993792), (871763605/9903520314283042199192993792)), (53/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-968425939/158456325028528675187087900672), (-341744243/79228162514264337593543950336)), (69/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((1317326023/2535301200456458802993406410752), (100150613/1267650600228229401496703205376)), (21/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-675088599/20282409603651670423947251286016), (218334447/20282409603651670423947251286016)), (97/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((514534219/324518553658426726783156020576256), (-1010901019/649037107316853453566312041152512)), (53/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((-457139227/10384593717069655257060992658440192), (665983613/5192296858534827628530496329220096)), (7/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5504000/1109451603), (-917440/369817201)), 0, by norm_num⟩
  | 1 => ⟨((-45437501235200/410294286466423203), (20198359040000/136764762155474401)), 0, by norm_num⟩
  | 2 => ⟨((38636643/35184372088832), (-425340271/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((128990927/2251799813685248), (883897417/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-666742493/144115188075855872), (-719044589/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((977571227/4611686018427387904), (367322271/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-1106110231/147573952589676412928), (115749651/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((249613079/1180591620717411303424), (-637107047/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-161894431/37778931862957161709568), (1082428391/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((101252789/4835703278458516698824704), (-1339477249/4835703278458516698824704)), (25/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((541564801/154742504910672534362390528), (1324098559/154742504910672534362390528)), (37/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-573266195/2475880078570760549798248448), (-501634111/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((196244619/19807040628566084398385987584), (409519385/158456325028528675187087900672)), (39/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((651849067/33554432), (293342415/16777216)), (7/33554432), by norm_num⟩
  | 1 => ⟨((719314893/536870912), (128546829/536870912)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((522867805/68719476736), (-135678517/34359738368)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-496211167/8796093022208), (704427599/8796093022208)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((255512619/1125899906842624), (-1872709385/1125899906842624)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((208613437/18014398509481984), (36606353/1125899906842624)), (15/18014398509481984), by norm_num⟩
  | 6 => ⟨((-332115941/576460752303423488), (-310123329/576460752303423488)), (43/1152921504606846976), by norm_num⟩
  | 7 => ⟨((684924349/36893488147419103232), (385038589/73786976294838206464)), (101/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-572711347/1180591620717411303424), (235584507/2361183241434822606848)), (129/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((775146569/75557863725914323419136), (-626072097/75557863725914323419136)), (23/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-88025189/604462909807314587353088), (798905767/2417851639229258349412352)), (245/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-47581279/77371252455336267181195264), (-780734123/77371252455336267181195264)), (159/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((364779781/2475880078570760549798248448), (613297649/2475880078570760549798248448)), (437/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-164849677/1125899906842624), (453696289/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((-412770967/18014398509481984), (-1414235867/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((266696997/72057594037927936), (575235671/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 3 => ⟨((-651714151/2305843009213693952), (-122440757/1152921504606846976)), (5/4611686018427387904), by norm_num⟩
  | 4 => ⟨((1106110231/73786976294838206464), (-115749651/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-698916621/1180591620717411303424), (445974933/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 6 => ⟨((604405875/37778931862957161709568), (-1010266499/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-60751673/604462909807314587353088), (803686349/604462909807314587353088)), (17/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-406173601/19342813113834066795298816), (-993073919/19342813113834066795298816)), (13/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((1050988023/618970019642690137449562112), (919662535/618970019642690137449562112)), (21/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-863476323/9903520314283042199192993792), (-112617831/4951760157141521099596496896)), (17/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((549401071/158456325028528675187087900672), (-232515999/316912650057057350374175801344)), (27/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-1091853015/10141204801825835211973625643008), (868988955/10141204801825835211973625643008)), (41/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((325924531/16777216), (586684857/33554432)), (1/4194304), by norm_num⟩
  | 1 => ⟨((1438629761/1073741824), (128546787/536870912)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1045736119/137438953472), (-542713519/137438953472)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-496213653/8796093022208), (704426665/8796093022208)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((255529497/1125899906842624), (-1872711151/1125899906842624)), (21/1125899906842624), by norm_num⟩
  | 5 => ⟨((417205545/36028797018963968), (585708453/18014398509481984)), (31/36028797018963968), by norm_num⟩
  | 6 => ⟨((-664213437/1152921504606846976), (-620277489/1152921504606846976)), (11/288230376151711744), by norm_num⟩
  | 7 => ⟨((684920641/36893488147419103232), (385136695/73786976294838206464)), (51/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-286368069/590295810358705651712), (117731641/1180591620717411303424)), (65/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((775274863/75557863725914323419136), (-312979917/37778931862957161709568)), (185/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-176155783/1208925819614629174706176), (399425389/1208925819614629174706176)), (123/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-47313017/77371252455336267181195264), (-1561581779/154742504910672534362390528)), (637/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((729026431/4951760157141521099596496896), (1227019609/4951760157141521099596496896)), (875/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-12699857/18014398509481984), (-438274797/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((1489632345/9223372036854775808), (559729173/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-632062989/36893488147419103232), (132285315/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 3 => ⟨((665634877/590295810358705651712), (-26546127/36893488147419103232)), (3/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-215859241/4722366482869645213696), (45101183/590295810358705651712)), (7/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((121503345/302231454903657293676544), (-803686349/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((541564803/4835703278458516698824704), (662049279/2417851639229258349412352)), (17/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-900846877/77371252455336267181195264), (-788282173/77371252455336267181195264)), (17/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((231288301/309485009821345068724781056), (241323923/1237940039285380274899124224)), (1/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-1438907567/39614081257132168796771975168), (76121309/9903520314283042199192993792)), (27/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((857884511/633825300114114700748351602688), (-170694259/158456325028528675187087900672)), (23/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-335408023/10141204801825835211973625643008), (1444057519/20282409603651670423947251286016)), (5/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-32573859/324518553658426726783156020576256), (-282500449/81129638414606681695789005144064)), (33/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((325924531/16777216), (586684857/33554432)), (9/33554432), by norm_num⟩
  | 1 => ⟨((1438629761/1073741824), (128546787/536870912)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((1045736117/137438953472), (-542713519/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-496213643/8796093022208), (704426659/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((127764723/562949953421312), (-1872711065/1125899906842624)), (11/562949953421312), by norm_num⟩
  | 5 => ⟨((417205559/36028797018963968), (585708357/18014398509481984)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-166053327/288230376151711744), (-620277173/1152921504606846976)), (45/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1369840423/73786976294838206464), (385135943/73786976294838206464)), (103/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1145470511/2361183241434822606848), (117731871/1180591620717411303424)), (131/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((775272119/75557863725914323419136), (-625959253/75557863725914323419136)), (93/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-352308293/2417851639229258349412352), (798848173/2417851639229258349412352)), (247/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-5914447/9671406556917033397649408), (-780785381/77371252455336267181195264)), (319/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((364512967/2475880078570760549798248448), (1227002367/4951760157141521099596496896)), (219/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1011300783/295147905179352825856), (-26457063/73786976294838206464)), (7/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-199690463/295147905179352825856), (254842819/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 2 => ⟨((259031089/4722366482869645213696), (-108242839/1180591620717411303424)), (11/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-121503345/151115727451828646838272), (200921587/18889465931478580854784)), (5/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((-203086801/604462909807314587353088), (-496536959/604462909807314587353088)), (7/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((945889221/19342813113834066795298816), (103462035/2417851639229258349412352)), (21/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-647607243/154742504910672534362390528), (-337853491/309485009821345068724781056)), (25/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((647508405/2475880078570760549798248448), (-274036713/4951760157141521099596496896)), (29/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-482560037/39614081257132168796771975168), (384062083/39614081257132168796771975168)), (29/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((461186031/1267650600228229401496703205376), (-124098693/158456325028528675187087900672)), (29/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((26873433/20282409603651670423947251286016), (1864502963/40564819207303340847894502572032)), (27/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-725807521/649037107316853453566312041152512), (-676277221/324518553658426726783156020576256)), (51/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((1001685013/10384593717069655257060992658440192), (706961829/10384593717069655257060992658440192)), (23/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((325924531/16777216), (586684857/33554432)), (5/16777216), by norm_num⟩
  | 1 => ⟨((1438629761/1073741824), (128546787/536870912)), (1/134217728), by norm_num⟩
  | 2 => ⟨((1045736117/137438953472), (-542713519/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-496213643/8796093022208), (704426659/8796093022208)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((127764723/562949953421312), (-936355533/562949953421312)), (23/1125899906842624), by norm_num⟩
  | 5 => ⟨((417205561/36028797018963968), (292854179/9007199254740992)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-664213313/1152921504606846976), (-310138587/576460752303423488)), (23/576460752303423488), by norm_num⟩
  | 7 => ⟨((684920221/36893488147419103232), (385135939/73786976294838206464)), (13/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-286367635/590295810358705651712), (235463765/2361183241434822606848)), (33/590295810358705651712), by norm_num⟩
  | 9 => ⟨((387636073/37778931862957161709568), (-39122457/4722366482869645213696)), (187/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-176154145/1208925819614629174706176), (199712071/604462909807314587353088)), (31/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-94631325/154742504910672534362390528), (-390392771/38685626227668133590597632)), (639/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((182256603/1237940039285380274899124224), (76687669/309485009821345068724781056)), (877/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-52329513/4722366482869645213696), (699751687/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((147276781/302231454903657293676544), (-1948330543/302231454903657293676544)), (15/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((246165819/604462909807314587353088), (1203725959/1208925819614629174706176)), (3/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-955443657/9671406556917033397649408), (-52253553/604462909807314587353088)), (13/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((490611547/38685626227668133590597632), (255949615/77371252455336267181195264)), (3/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-1373502675/1237940039285380274899124224), (290644999/1237940039285380274899124224)), (37/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((682408133/9903520314283042199192993792), (-543118097/9903520314283042199192993792)), (27/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((-104815007/39614081257132168796771975168), (902535949/158456325028528675187087900672)), (33/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((-30537993/2535301200456458802993406410752), (-264844171/633825300114114700748351602688)), (39/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((504033001/40564819207303340847894502572032), (469636959/20282409603651670423947251286016)), (43/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-834737511/649037107316853453566312041152512), (-589134857/649037107316853453566312041152512)), (23/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((1858046623/20769187434139310514121985316880384), (282518535/20769187434139310514121985316880384)), (91/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((-793492569/166153499473114484112975882535043072), (513256367/332306998946228968225951765070086144)), (89/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((325924531/16777216), (586684857/33554432)), (11/33554432), by norm_num⟩
  | 1 => ⟨((1438629761/1073741824), (128546787/536870912)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((1045736117/137438953472), (-542713519/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-496213643/8796093022208), (704426659/8796093022208)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((127764723/562949953421312), (-936355533/562949953421312)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((417205561/36028797018963968), (292854179/9007199254740992)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-664213313/1152921504606846976), (-310138587/576460752303423488)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((684920221/36893488147419103232), (385135939/73786976294838206464)), (105/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-286367635/590295810358705651712), (58865941/590295810358705651712)), (133/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((775272147/75557863725914323419136), (-312979655/37778931862957161709568)), (47/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-352308293/2417851639229258349412352), (399424141/1208925819614629174706176)), (249/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-94631311/154742504910672534362390528), (-780785541/77371252455336267181195264)), (5/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((182256597/1237940039285380274899124224), (153375339/618970019642690137449562112)), (439/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-12461581/151115727451828646838272), (-974973937/4835703278458516698824704)), (27/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((580405773/9671406556917033397649408), (507881567/9671406556917033397649408)), (3/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((-1192132145/77371252455336267181195264), (-155482359/38685626227668133590597632)), (41/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((1390608569/618970019642690137449562112), (-294264753/618970019642690137449562112)), (13/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((-1036360483/4951760157141521099596496896), (412411653/2475880078570760549798248448)), (27/2475880078570760549798248448), by norm_num⟩
  | 5 => ⟨((111426415/9903520314283042199192993792), (-479732569/19807040628566084398385987584)), (47/39614081257132168796771975168), by norm_num⟩
  | 6 => ⟨((2705353/39614081257132168796771975168), (750799269/316912650057057350374175801344)), (37/316912650057057350374175801344), by norm_num⟩
  | 7 => ⟨((-229639651/2535301200456458802993406410752), (-855874651/5070602400912917605986812821504)), (53/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((237693799/20282409603651670423947251286016), (167757769/20282409603651670423947251286016)), (69/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((-1293316151/1298074214633706907132624082305024), (-49162623/324518553658426726783156020576256)), (21/324518553658426726783156020576256), by norm_num⟩
  | 10 => ⟨((662784287/10384593717069655257060992658440192), (-428710071/20769187434139310514121985316880384)), (3/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((-252578103/83076749736557242056487941267521536), (248119029/83076749736557242056487941267521536)), (105/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((112201827/1329227995784915872903807060280344576), (-1307690501/5316911983139663491615228241121378304)), (111/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((325924531/16777216), (586684857/33554432)), (3/8388608), by norm_num⟩
  | 1 => ⟨((1438629761/1073741824), (128546787/536870912)), (5/536870912), by norm_num⟩
  | 2 => ⟨((1045736117/137438953472), (-542713519/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-496213643/8796093022208), (704426659/8796093022208)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((127764723/562949953421312), (-936355533/562949953421312)), (25/1125899906842624), by norm_num⟩
  | 5 => ⟨((417205561/36028797018963968), (292854179/9007199254740992)), (35/36028797018963968), by norm_num⟩
  | 6 => ⟨((-664213313/1152921504606846976), (-310138587/576460752303423488)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((684920221/36893488147419103232), (385135939/73786976294838206464)), (53/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-286367635/590295810358705651712), (58865941/590295810358705651712)), (67/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((775272147/75557863725914323419136), (-312979655/37778931862957161709568)), (189/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-352308293/2417851639229258349412352), (399424141/1208925819614629174706176)), (125/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-94631311/154742504910672534362390528), (-780785541/77371252455336267181195264)), (641/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((182256597/1237940039285380274899124224), (1227002711/4951760157141521099596496896)), (879/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((234385966097935/4194304), (-561355907510949/2097152)), (1000295569/4194304), by norm_num⟩
  | 1 => ⟨(138963645, (-690517645/2)), (1519/4), by norm_num⟩
  | 2 => ⟨(133795799, -216914595), (1221/4), by norm_num⟩
  | 3 => ⟨((615049695/8), (-706360967/8)), (1319/8), by norm_num⟩
  | 4 => ⟨((498117593/16), -26039610), (1077/16), by norm_num⟩
  | 5 => ⟨((1240238685/128), (-93816187/16)), (2837/128), by norm_num⟩
  | 6 => ⟨((625539325/256), (-65556283/64)), (785/128), by norm_num⟩
  | 7 => ⟨((1059342291/2048), (-68884941/512)), (3003/2048), by norm_num⟩
  | 8 => ⟨((772081407/8192), (-180632189/16384)), (5067/16384), by norm_num⟩
  | 9 => ⟨((1973840361/131072), (17161821/65536)), (3831/65536), by norm_num⟩
  | 10 => ⟨((1122119101/524288), (41622759/131072)), (2629/262144), by norm_num⟩
  | 11 => ⟨((1147457459/4194304), (321915453/4194304)), (3309/2097152), by norm_num⟩
  | 12 => ⟨((1064476325/33554432), (445363891/33554432)), (7701/33554432), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1609281103300043/10141204801825835211973625643008), (-1778044938233/10141204801825835211973625643008)), (465851/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1812500529844079/633825300114114700748351602688), (-1089446014163/316912650057057350374175801344)), (572115/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1927728629280691/39614081257132168796771975168), (-2457386662105/39614081257132168796771975168)), (645387/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1929914285420365/2475880078570760549798248448), (-654067075179/618970019642690137449562112)), (687215/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((905810705624117/77371252455336267181195264), (-1311097978335/77371252455336267181195264)), (688883/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((793750372413737/4835703278458516698824704), (-2464624857155/9671406556917033397649408)), (323803/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1292036202452571/604462909807314587353088), (-540721070771/151115727451828646838272)), (568439/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((60684414058613/2361183241434822606848), (-1763307749821/37778931862957161709568)), (28971/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1338193305740783/4722366482869645213696), (-1327722484255/2361183241434822606848)), (349129/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1677464474475841/590295810358705651712), (-917089678519/147573952589676412928)), (15077/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1893671733452413/73786976294838206464), (-4611283385299/73786976294838206464)), (1213443/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1901872687155291/9223372036854775808), (-5223465866065/9223372036854775808)), (343803/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1673427953879635/1152921504606846976), (-329284830743/72057594037927936)), (693969/576460752303423488), by norm_num⟩
  | 5 => ⟨((632220038779037/72057594037927936), (-4661237788381/144115188075855872)), (1228919/144115188075855872), by norm_num⟩
  | 4 => ⟨((1597127333561101/36028797018963968), (-1773919338095/9007199254740992)), (468181/9007199254740992), by norm_num⟩
  | 3 => ⟨((811180199129093/4503599627370496), (-9054294257673/9007199254740992)), (598293/2251799813685248), by norm_num⟩
  | 2 => ⟨((1248964802645169/2251799813685248), (-9337466307957/2251799813685248)), (618357/562949953421312), by norm_num⟩
  | 1 => ⟨((1315356266120101/1125899906842624), (-14736040503285/1125899906842624)), (3917427/1125899906842624), by norm_num⟩
  | 0 => ⟨((1524850008030757/1125899906842624), (-32526758465081/1125899906842624)), (8705121/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1524850008030757/1125899906842624), (-32526758465081/1125899906842624)), (33207401279929732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1032111976762075/562949953421312), (-88104506635555/1125899906842624)), (24082343/1125899906842624), by norm_num⟩
  | 2 => ⟨((1888826040558457/562949953421312), (-40382682311555/140737488355328)), (46037053/562949953421312), by norm_num⟩
  | 3 => ⟨((786386874507477/70368744177664), (-270986298068239/140737488355328)), (83837279/140737488355328), by norm_num⟩
  | 4 => ⟨((1065895679208595/8796093022208), (-5914715050299/137438953472)), (34322729/2199023255552), by norm_num⟩
  | 5 => ⟨((881818824586933/68719476736), (-358367584332413/34359738368)), (176133019/34359738368), by norm_num⟩
  | 6 => ⟨((234385966097935/4194304), (-561355907510949/2097152)), (1000295569/4194304), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((325924531/16777216), (586684857/33554432)), (3/8388608), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2355200/77362801), (-11009280/77362801)), 0, by norm_num⟩
  | 1 => ⟨((57828639539200/5985002978565601), (25929056256000/5985002978565601)), 0, by norm_num⟩
  | 2 => ⟨((-250324803/549755813888), (683410527/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-164025289/4398046511104), (-736411823/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((998165865/281474976710656), (-567591053/281474976710656)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((201538131/2251799813685248), (1274605137/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1549252081/72057594037927936), (74228409/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((6509575/36028797018963968), (-1799913677/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((249799001/2305843009213693952), (168878585/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-627874855/147573952589676412928), (263820409/36893488147419103232)), (15/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-262118745/590295810358705651712), (-971821007/2361183241434822606848)), (11/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((680865619/18889465931478580854784), (-478479149/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((189452097/151115727451828646838272), (891669301/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((23/16), (8601/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((23/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((23/16), (8601/1280)))⁻¹=value ((2355200/77362801), (-11009280/77362801)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2355200/77362801), (-11009280/77362801))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1331200/27903867), (-3669760/27903867)), 0, by norm_num⟩
  | 1 => ⟨((649724723200/86513977061521), (4885184512000/778625793553689)), 0, by norm_num⟩
  | 2 => ⟨((-1301178999/2199023255552), (756863651/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-149854279/17592186044416), (-207231189/4398046511104)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((464658311/140737488355328), (158697831/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-130411261/1125899906842624), (458590261/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-765891985/72057594037927936), (-224718877/18014398509481984)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((154753203/144115188075855872), (-231373909/576460752303423488)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((14367535/18446744073709551616), (1479154645/18446744073709551616)), (17/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-780862181/147573952589676412928), (-137351949/73786976294838206464)), (25/295147905179352825856), by norm_num⟩
  | 10 => ⟨((587038667/2361183241434822606848), (-179178819/590295810358705651712)), (19/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((265010893/18889465931478580854784), (891168925/37778931862957161709568)), (7/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-1139896797/604462909807314587353088), (54381615/151115727451828646838272)), (41/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((39/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((39/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((39/16), (8601/1280)))⁻¹=value ((1331200/27903867), (-3669760/27903867)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((1331200/27903867), (-3669760/27903867))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-37266173132800/2158721309851467), (-23298572288000/2158721309851467)), 0, by norm_num⟩
  | 1 => ⟨((295796455/137438953472), (-133437607/68719476736)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((599759573/4398046511104), (609957403/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-1012493753/35184372088832), (23128233/4398046511104)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((137698487/562949953421312), (-1452577767/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((924721305/4503599627370496), (178712307/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-783360095/72057594037927936), (1047332325/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((-128714903/144115188075855872), (-668582929/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 8 => ⟨((992012237/9223372036854775808), (-50227519/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 9 => ⟨((76493663/73786976294838206464), (1329985533/147573952589676412928)), (9/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-817756823/1180591620717411303424), (-127552865/1180591620717411303424)), (7/590295810358705651712), by norm_num⟩
  | 11 => ⟨((207927363/9444732965739290427392), (-924063611/18889465931478580854784)), (11/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((59303287/18889465931478580854784), (391453035/151115727451828646838272)), (33/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((55/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5632000/93337201), (-11009280/93337201)), 0, by norm_num⟩
  | 1 => ⟨((44742411059200/8711833090514401), (62004264960000/8711833090514401)), 0, by norm_num⟩
  | 2 => ⟨((-1263765985/2199023255552), (193867511/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((53389091/4398046511104), (-1286090883/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((251848901/140737488355328), (15997731/8796093022208)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-1452416045/9007199254740992), (456353957/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((270492677/144115188075855872), (-1590811827/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((685269235/1152921504606846976), (511580879/1152921504606846976)), (9/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-6355701/144115188075855872), (199838749/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((31136643/590295810358705651712), (-960591071/295147905179352825856)), (41/590295810358705651712), by norm_num⟩
  | 10 => ⟨((3511373/18446744073709551616), (478389741/4722366482869645213696)), (15/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-885340121/75557863725914323419136), (308647663/37778931862957161709568)), (11/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-77557137/604462909807314587353088), (-70837589/75557863725914323419136)), (1/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((55/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((55/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((55/16), (8601/1280)))⁻¹=value ((5632000/93337201), (-11009280/93337201)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((5632000/93337201), (-11009280/93337201))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-318127895/137438953472), (761395169/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((-122063377/1099511627776), (-603982023/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((1349171201/17592186044416), (187845051/17592186044416)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-285672467/70368744177664), (556784493/70368744177664)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((-713539153/1125899906842624), (-746118645/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((360079163/4503599627370496), (-663157859/18014398509481984)), (5/9007199254740992), by norm_num⟩
  | 6 => ⟨((29444557/36028797018963968), (1150801919/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((-395618903/576460752303423488), (-362837161/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((578063605/18446744073709551616), (-470779363/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((941633667/295147905179352825856), (140549237/36893488147419103232)), (3/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-886548285/2361183241434822606848), (10950069/73786976294838206464)), (19/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-70491197/37778931862957161709568), (-607662121/18889465931478580854784)), (31/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1480022421/604462909807314587353088), (97698121/151115727451828646838272)), (3/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((71/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7270400/106239601), (-11009280/106239601)), 0, by norm_num⟩
  | 1 => ⟨((34172764979200/11286852820639201), (80041869312000/11286852820639201)), 0, by norm_num⟩
  | 2 => ⟨((-258955781/549755813888), (-47157923/549755813888)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((723462623/35184372088832), (-755442517/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((115098909/281474976710656), (253336265/140737488355328)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-60381579/562949953421312), (-90985125/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((830627711/144115188075855872), (-300834351/72057594037927936)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((88094231/4611686018427387904), (1017999695/2305843009213693952)), (25/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-868051741/36893488147419103232), (-520810537/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 9 => ⟨((453496899/295147905179352825856), (-217249451/295147905179352825856)), (13/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-136347473/9444732965739290427392), (989787565/9444732965739290427392)), (37/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-745902483/151115727451828646838272), (-163728759/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((951295171/2417851639229258349412352), (-259816865/2417851639229258349412352)), (73/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((71/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((71/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((71/16), (8601/1280)))⁻¹=value ((7270400/106239601), (-11009280/106239601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7270400/106239601), (-11009280/106239601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-65456239/4398046511104), (183971735/549755813888)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-1431144907/17592186044416), (-673946411/17592186044416)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((782735749/70368744177664), (-89023783/8796093022208)), (5/70368744177664), by norm_num⟩
  | 3 => ⟨((12066577/17592186044416), (1061052683/562949953421312)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-525052671/2251799813685248), (-1214575/140737488355328)), (7/4503599627370496), by norm_num⟩
  | 5 => ⟨((90813319/9007199254740992), (-406956829/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((492566023/288230376151711744), (253233317/144115188075855872)), (15/576460752303423488), by norm_num⟩
  | 7 => ⟨((-122665527/576460752303423488), (409381711/4611686018427387904)), (7/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-34182607/73786976294838206464), (-1535007887/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 9 => ⟨((1007543813/590295810358705651712), (364754299/590295810358705651712)), (11/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-951424587/9444732965739290427392), (274743757/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-228311447/37778931862957161709568), (-211732777/18889465931478580854784)), (15/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1235667857/1208925819614629174706176), (-168129567/1208925819614629174706176)), (3/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((87/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2969600/40806267), (-3669760/40806267)), 0, by norm_num⟩
  | 1 => ⟨((774769049600/555050475491763), (10897719296000/1665151426475289)), 0, by norm_num⟩
  | 2 => ⟨((-758820525/2199023255552), (-385641431/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((719223825/35184372088832), (-160709473/17592186044416)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-374952869/1125899906842624), (1409142189/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((-795515767/18014398509481984), (-1090141509/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 6 => ⟨((623720011/144115188075855872), (62330089/288230376151711744)), (5/144115188075855872), by norm_num⟩
  | 7 => ⟨((-385542187/2305843009213693952), (430591709/2305843009213693952)), (7/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-170664825/73786976294838206464), (-528062503/36893488147419103232)), (19/73786976294838206464), by norm_num⟩
  | 9 => ⟨((859187941/1180591620717411303424), (492075371/1180591620717411303424)), (13/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-854230165/18889465931478580854784), (331664059/18889465931478580854784)), (35/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((517408525/604462909807314587353088), (-807665995/302231454903657293676544)), (23/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((430461759/4835703278458516698824704), (164083987/1208925819614629174706176)), (61/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((87/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((87/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((87/16), (8601/1280)))⁻¹=value ((2969600/40806267), (-3669760/40806267)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((2969600/40806267), (-3669760/40806267))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((255190119/8796093022208), (451968655/17592186044416)), (3/35184372088832), by norm_num⟩
  | 1 => ⟨((-407303629/35184372088832), (86163493/17592186044416)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((56456997/562949953421312), (-1371126907/562949953421312)), (9/562949953421312), by norm_num⟩
  | 3 => ⟨((732484323/2251799813685248), (189840299/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 4 => ⟨((-334730217/9007199254740992), (259703201/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-358026965/288230376151711744), (-759612607/144115188075855872)), (9/144115188075855872), by norm_num⟩
  | 6 => ⟨((1301864629/2305843009213693952), (126962195/1152921504606846976)), (9/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-608697339/18446744073709551616), (108321611/2305843009213693952)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-415606407/147573952589676412928), (-688483141/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1161789017/2361183241434822606848), (-38611277/590295810358705651712)), (15/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-13965135/1180591620717411303424), (1587919841/37778931862957161709568)), (51/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-439355959/151115727451828646838272), (-705263743/302231454903657293676544)), (43/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((82386777/302231454903657293676544), (-44689847/302231454903657293676544)), (9/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((103/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((10547200/141874801), (-11009280/141874801)), 0, by norm_num⟩
  | 1 => ⟨((4980409139200/20128459158789601), (116117078016000/20128459158789601)), 0, by norm_num⟩
  | 2 => ⟨((-1024843977/4398046511104), (-900855413/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((584374497/35184372088832), (-100443043/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-632739499/1125899906842624), (196320667/281474976710656)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-55591739/9007199254740992), (-1719661511/36028797018963968)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((1199794957/576460752303423488), (884696293/576460752303423488)), (13/576460752303423488), by norm_num⟩
  | 7 => ⟨((-39461459/288230376151711744), (27332619/1152921504606846976)), (17/9223372036854775808), by norm_num⟩
  | 8 => ⟨((19227081/4611686018427387904), (-456977919/73786976294838206464)), (11/73786976294838206464), by norm_num⟩
  | 9 => ⟨((201454009/2361183241434822606848), (925509933/2361183241434822606848)), (7/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-694357201/37778931862957161709568), (-106342701/9444732965739290427392)), (35/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1354044605/1208925819614629174706176), (-178066965/604462909807314587353088)), (43/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-292105463/9671406556917033397649408), (32886869/604462909807314587353088)), (105/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((103/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((103/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((103/16), (8601/1280)))⁻¹=value ((10547200/141874801), (-11009280/141874801)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((10547200/141874801), (-11009280/141874801))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((146029201/35184372088832), (-96075147/281474976710656)), (5/281474976710656), by norm_num⟩
  | 1 => ⟨((-87477381/140737488355328), (808471441/562949953421312)), (3/281474976710656), by norm_num⟩
  | 2 => ⟨((-482248237/2251799813685248), (-599762083/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 3 => ⟨((500450459/9007199254740992), (-100123641/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-9724603/4503599627370496), (273680509/36028797018963968)), (15/144115188075855872), by norm_num⟩
  | 5 => ⟨((-825282695/1152921504606846976), (-381380671/576460752303423488)), (17/1152921504606846976), by norm_num⟩
  | 6 => ⟨((948115547/9223372036854775808), (-357926077/9223372036854775808)), (9/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-165732879/147573952589676412928), (1694701201/147573952589676412928)), (19/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-575659625/590295810358705651712), (-706849593/1180591620717411303424)), (9/295147905179352825856), by norm_num⟩
  | 9 => ⟨((107412983/1180591620717411303424), (-4325851/73786976294838206464)), (33/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((48168171/37778931862957161709568), (1473659133/151115727451828646838272)), (29/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-994918885/1208925819614629174706176), (-78846717/302231454903657293676544)), (25/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((239385217/4835703278458516698824704), (-1051849483/19342813113834066795298816)), (85/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((119/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12185600/164607601), (-11009280/164607601)), 0, by norm_num⟩
  | 1 => ⟨((-13642300620800/27095662306975201), (134154682368000/27095662306975201)), 0, by norm_num⟩
  | 2 => ⟨((-323113971/2199023255552), (-880046339/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((213396607/17592186044416), (43854455/17592186044416)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-599373861/1125899906842624), (705658845/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((41545253/4503599627370496), (-529652959/18014398509481984)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((369954473/576460752303423488), (805180061/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 7 => ⟨((-649912635/9223372036854775808), (-69725453/2305843009213693952)), (11/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1068245547/295147905179352825856), (-365133491/295147905179352825856)), (13/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-437275365/4722366482869645213696), (787812223/4722366482869645213696)), (15/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-10159867/4722366482869645213696), (-700529087/75557863725914323419136)), (69/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((58886625/151115727451828646838272), (81973397/302231454903657293676544)), (39/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-908869153/38685626227668133590597632), (28937051/9671406556917033397649408)), (177/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((119/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((119/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((119/16), (8601/1280)))⁻¹=value ((12185600/164607601), (-11009280/164607601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12185600/164607601), (-11009280/164607601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((640452041/2251799813685248), (-340984113/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 1 => ⟨((223551855/4503599627370496), (1518675921/9007199254740992)), (1/562949953421312), by norm_num⟩
  | 2 => ⟨((-1482352179/36028797018963968), (-359372555/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 3 => ⟨((753158211/144115188075855872), (-799207163/144115188075855872)), (9/72057594037927936), by norm_num⟩
  | 4 => ⟨((392234761/1152921504606846976), (1252970919/1152921504606846976)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((-674111757/4611686018427387904), (-276241261/9223372036854775808)), (7/2305843009213693952), by norm_num⟩
  | 6 => ⟨((843116027/73786976294838206464), (-998156379/73786976294838206464)), (31/73786976294838206464), by norm_num⟩
  | 7 => ⟨((6588773/9223372036854775808), (1067284503/590295810358705651712)), (33/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-470207893/2361183241434822606848), (-209044201/9444732965739290427392)), (65/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((412749839/37778931862957161709568), (-153621269/9444732965739290427392)), (31/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((66955067/75557863725914323419136), (484790845/302231454903657293676544)), (7/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-398491483/2417851639229258349412352), (57943587/9671406556917033397649408)), (99/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((458632979/77371252455336267181195264), (-1011222981/77371252455336267181195264)), (85/77371252455336267181195264), by norm_num⟩
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
  | 0 => ⟨((135/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1536000/21179689), (-3669760/63539067)), 0, by norm_num⟩
  | 1 => ⟨((-3883262771200/4037213035230489), (1878917120000/448579226136721)), 0, by norm_num⟩
  | 2 => ⟨((-189291437/2199023255552), (-790153529/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((73091783/8796093022208), (567013469/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-940487757/2251799813685248), (211381229/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((111995639/9007199254740992), (-557189051/36028797018963968)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((-9847687/2305843009213693952), (265129207/288230376151711744)), (19/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-487152657/18446744073709551616), (-617564103/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 8 => ⟨((567979569/295147905179352825856), (133209643/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-391078739/4722366482869645213696), (92574143/2361183241434822606848)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((565392529/302231454903657293676544), (-576232173/151115727451828646838272)), (55/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((25558115/604462909807314587353088), (929873345/4835703278458516698824704)), (59/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-1096543985/154742504910672534362390528), (-445019967/77371252455336267181195264)), (31/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((135/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((135/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((135/16), (8601/1280)))⁻¹=value ((1536000/21179689), (-3669760/63539067)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((1536000/21179689), (-3669760/63539067))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((28237323/9007199254740992), (-691582691/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((516397691/36028797018963968), (781353707/72057594037927936)), (19/72057594037927936), by norm_num⟩
  | 2 => ⟨((-633066601/144115188075855872), (30149139/18014398509481984)), (25/288230376151711744), by norm_num⟩
  | 3 => ⟨((195618811/1152921504606846976), (-128487355/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((123402593/1152921504606846976), (111136327/1152921504606846976)), (17/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-1401630183/73786976294838206464), (216415127/36893488147419103232)), (21/36893488147419103232), by norm_num⟩
  | 6 => ⟨((334565651/590295810358705651712), (-1418038091/590295810358705651712)), (47/590295810358705651712), by norm_num⟩
  | 7 => ⟨((484166799/2361183241434822606848), (456514401/2361183241434822606848)), (13/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-1085737801/37778931862957161709568), (332723801/37778931862957161709568)), (53/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((96820443/151115727451828646838272), (-894572065/302231454903657293676544)), (51/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((529874401/2417851639229258349412352), (923521759/4835703278458516698824704)), (95/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-242445827/9671406556917033397649408), (361976481/38685626227668133590597632)), (85/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((48563187/154742504910672534362390528), (-1456697257/618970019642690137449562112)), (149/618970019642690137449562112), by norm_num⟩
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
  | 0 => ⟨((151/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((15462400/219903601), (-11009280/219903601)), 0, by norm_num⟩
  | 1 => ⟨((-58940783820800/48357593732767201), (170229891072000/48357593732767201)), 0, by norm_num⟩
  | 2 => ⟨((-199087031/4398046511104), (-1356990279/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((383735645/70368744177664), (603854295/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-673566017/2251799813685248), (-16147627/1125899906842624)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((391826041/36028797018963968), (-503210659/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-119637057/576460752303423488), (596926639/1152921504606846976)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-52240717/9223372036854775808), (-1726451645/73786976294838206464)), (13/36893488147419103232), by norm_num⟩
  | 8 => ⟨((115819497/147573952589676412928), (401885633/590295810358705651712)), (13/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-1686245933/37778931862957161709568), (-162072373/37778931862957161709568)), (51/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1013451681/604462909807314587353088), (-146048775/151115727451828646838272)), (25/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-672209299/19342813113834066795298816), (183629841/2417851639229258349412352)), (97/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-52560209/77371252455336267181195264), (-1095585691/309485009821345068724781056)), (95/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((151/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((151/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((151/16), (8601/1280)))⁻¹=value ((15462400/219903601), (-11009280/219903601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((15462400/219903601), (-11009280/219903601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-61304989/36028797018963968), (-823289721/288230376151711744)), (1/18014398509481984), by norm_num⟩
  | 1 => ⟨((969608049/576460752303423488), (118422843/1152921504606846976)), (5/144115188075855872), by norm_num⟩
  | 2 => ⟨((-661301355/2305843009213693952), (867210815/2305843009213693952)), (7/576460752303423488), by norm_num⟩
  | 3 => ⟨((-147741191/4611686018427387904), (-105590851/1152921504606846976)), (29/9223372036854775808), by norm_num⟩
  | 4 => ⟨((1163688081/73786976294838206464), (70786589/18446744073709551616)), (43/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-249770727/147573952589676412928), (479121877/295147905179352825856)), (55/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-72659725/1180591620717411303424), (-1401252723/4722366482869645213696)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((318184243/9444732965739290427392), (230836845/18889465931478580854784)), (71/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-927904559/302231454903657293676544), (747038869/302231454903657293676544)), (75/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-538987/9444732965739290427392), (-488347897/1208925819614629174706176)), (37/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((1434803219/38685626227668133590597632), (73649475/4835703278458516698824704)), (35/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-922081795/309485009821345068724781056), (356820455/154742504910672534362390528)), (129/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-120646489/2475880078570760549798248448), (-833977729/2475880078570760549798248448)), (57/1237940039285380274899124224), by norm_num⟩
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
  | 0 => ⟨((167/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((17100800/252466801), (-11009280/252466801)), 0, by norm_num⟩
  | 1 => ⟨((-85616557260800/63739485607173601), (188267495424000/63739485607173601)), 0, by norm_num⟩
  | 2 => ⟨((-83163585/4398046511104), (-1137521587/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((486958959/140737488355328), (558374779/140737488355328)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-917328821/4503599627370496), (-265386997/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((1179325053/144115188075855872), (-352413853/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((-32256873/144115188075855872), (602378719/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((139052729/73786976294838206464), (-1012927297/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 8 => ⟨((139007383/590295810358705651712), (597393003/1180591620717411303424)), (27/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-22440855/1180591620717411303424), (-113363909/9444732965739290427392)), (25/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1094634563/1208925819614629174706176), (-9594345/1208925819614629174706176)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1179624399/38685626227668133590597632), (387067427/19342813113834066795298816)), (83/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((46144101/77371252455336267181195264), (-415502403/309485009821345068724781056)), (75/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((167/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((167/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((167/16), (8601/1280)))⁻¹=value ((17100800/252466801), (-11009280/252466801)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((17100800/252466801), (-11009280/252466801))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-276483749/1152921504606846976), (-275030935/2305843009213693952)), (29/4611686018427387904), by norm_num⟩
  | 1 => ⟨((1191029205/9223372036854775808), (-311650939/4611686018427387904)), (39/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-109308517/18446744073709551616), (1589555045/36893488147419103232)), (57/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-1018620131/147573952589676412928), (-943721123/147573952589676412928)), (61/147573952589676412928), by norm_num⟩
  | 4 => ⟨((949652369/590295810358705651712), (-213519107/590295810358705651712)), (3/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-213574299/2361183241434822606848), (136410357/590295810358705651712)), (65/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-720942923/37778931862957161709568), (-257024065/9444732965739290427392)), (39/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((1225386161/302231454903657293676544), (-41029561/302231454903657293676544)), (11/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-141763107/604462909807314587353088), (119170727/302231454903657293676544)), (95/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-53518751/2417851639229258349412352), (-419164659/9671406556917033397649408)), (3/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1507493709/309485009821345068724781056), (123645495/309485009821345068724781056)), (23/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-680706115/2475880078570760549798248448), (937827191/2475880078570760549798248448)), (43/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-20966593/1237940039285380274899124224), (-195663707/4951760157141521099596496896)), (39/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((183/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((102400/1575447), (-60160/1575447)), 0, by norm_num⟩
  | 1 => ⟨((-1144422400/827344416603), (6160384000/2482033249809)), 0, by norm_num⟩
  | 2 => ⟨((-9521070080000/3910311837311839623), (-418684338176000/3910311837311839623)), 0, by norm_num⟩
  | 3 => ⟨((298849321/140737488355328), (483181163/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-606002987/4503599627370496), (-639797613/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((825668581/144115188075855872), (-75143157/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-208926499/1152921504606846976), (543536421/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((537012217/147573952589676412928), (-537925819/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 8 => ⟨((98848731/4722366482869645213696), (723471435/2361183241434822606848)), (13/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-1927433/295147905179352825856), (-722183407/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((954376031/2417851639229258349412352), (112392895/604462909807314587353088)), (21/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-1267189127/77371252455336267181195264), (115564735/77371252455336267181195264)), (9/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((623608625/1237940039285380274899124224), (-894404463/2475880078570760549798248448)), (15/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((183/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((183/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((183/16), (8601/1280)))⁻¹=value ((102400/1575447), (-60160/1575447)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((102400/1575447), (-60160/1575447))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1486201345/73786976294838206464), (103657833/73786976294838206464)), (49/73786976294838206464), by norm_num⟩
  | 1 => ⟨((475219971/73786976294838206464), (-44980871/4611686018427387904)), (35/73786976294838206464), by norm_num⟩
  | 2 => ⟨((365101779/295147905179352825856), (1023170747/295147905179352825856)), (53/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-235889951/295147905179352825856), (-142331405/590295810358705651712)), (59/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((35810647/295147905179352825856), (-109047419/1180591620717411303424)), (97/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((57848355/75557863725914323419136), (1797711849/75557863725914323419136)), (17/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-833761239/302231454903657293676544), (-543624837/302231454903657293676544)), (85/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((924446281/2417851639229258349412352), (-381690301/2417851639229258349412352)), (49/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-185659493/19342813113834066795298816), (909397377/19342813113834066795298816)), (107/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-569364045/154742504910672534362390528), (-569911655/154742504910672534362390528)), (111/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((1291796587/2475880078570760549798248448), (-273819483/2475880078570760549798248448)), (27/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-361487845/19807040628566084398385987584), (964102673/19807040628566084398385987584)), (205/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-233402231/79228162514264337593543950336), (-305177799/79228162514264337593543950336)), (189/158456325028528675187087900672), by norm_num⟩
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
  | 0 => ⟨((199/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((20377600/327423601), (-11009280/327423601)), 0, by norm_num⟩
  | 1 => ⟨((-147021167820800/107206214491807201), (224342704128000/107206214491807201)), 0, by norm_num⟩
  | 2 => ⟨((4119717/549755813888), (-1551179167/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((175808555/140737488355328), (807777381/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-392351929/4503599627370496), (-307601849/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1112361163/288230376151711744), (47612333/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-302531165/2305843009213693952), (51098303/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((985096591/295147905179352825856), (-1058088049/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-411704797/9444732965739290427392), (1583587701/9444732965739290427392)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-110494231/75557863725914323419136), (-224799251/37778931862957161709568)), (3/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((703808817/4835703278458516698824704), (388256753/2417851639229258349412352)), (19/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-1118589575/154742504910672534362390528), (-49324809/19342813113834066795298816)), (59/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((663077821/2475880078570760549798248448), (-208849747/4951760157141521099596496896)), (91/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((199/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((199/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((199/16), (8601/1280)))⁻¹=value ((20377600/327423601), (-11009280/327423601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((20377600/327423601), (-11009280/327423601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-178020267/147573952589676412928), (225693011/295147905179352825856)), (39/590295810358705651712), by norm_num⟩
  | 1 => ⟨((57585273/590295810358705651712), (-128044031/147573952589676412928)), (57/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((484279847/2361183241434822606848), (957681955/4722366482869645213696)), (45/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-159710269/2361183241434822606848), (170086937/18889465931478580854784)), (13/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((483487273/75557863725914323419136), (-849689771/75557863725914323419136)), (45/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((253144915/302231454903657293676544), (578027077/302231454903657293676544)), (65/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-351056489/1208925819614629174706176), (-312480307/4835703278458516698824704)), (21/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((1106803325/38685626227668133590597632), (-988488291/38685626227668133590597632)), (99/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((161779551/309485009821345068724781056), (1400380177/309485009821345068724781056)), (55/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-275545853/618970019642690137449562112), (-294028193/1237940039285380274899124224)), (29/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((922990859/19807040628566084398385987584), (-485659999/19807040628566084398385987584)), (231/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-170199789/316912650057057350374175801344), (822294897/158456325028528675187087900672)), (443/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-121501943/316912650057057350374175801344), (-788949541/2535301200456458802993406410752)), (207/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((301869295/2199023255552), (804032731/2199023255552)), (541/1099511627776), by norm_num⟩
  | 1 => ⟨((-71700031/549755813888), (492749641/1099511627776)), (1129/1099511627776), by norm_num⟩
  | 2 => ⟨((-949078763/4398046511104), (182689809/1099511627776)), (4919/4398046511104), by norm_num⟩
  | 3 => ⟨((-908038293/8796093022208), (70865109/17592186044416)), (14631/17592186044416), by norm_num⟩
  | 4 => ⟨((-853769443/35184372088832), (-133654135/8796093022208)), (16577/35184372088832), by norm_num⟩
  | 5 => ⟨((-92121271/35184372088832), (-394111795/70368744177664)), (30425/140737488355328), by norm_num⟩
  | 6 => ⟨((128522449/1125899906842624), (-607703745/562949953421312)), (5883/70368744177664), by norm_num⟩
  | 7 => ⟨((825430669/9007199254740992), (-295861331/2251799813685248)), (252365/9007199254740992), by norm_num⟩
  | 8 => ⟨((646170943/36028797018963968), (-711268551/72057594037927936)), (598445/72057594037927936), by norm_num⟩
  | 9 => ⟨((669200427/288230376151711744), (-30342509/144115188075855872)), (637435/288230376151711744), by norm_num⟩
  | 10 => ⟨((268231055/1152921504606846976), (156110681/2305843009213693952)), (2470169/4611686018427387904), by norm_num⟩
  | 11 => ⟨((347699511/18446744073709551616), (505922059/36893488147419103232)), (4397107/36893488147419103232), by norm_num⟩
  | 12 => ⟨((711615725/590295810358705651712), (502164421/295147905179352825856)), (14502055/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((301869295/2199023255552), (804032731/2199023255552)), (1083/2199023255552), by norm_num⟩
  | 1 => ⟨((-71700031/549755813888), (492749641/1099511627776)), (2259/2199023255552), by norm_num⟩
  | 2 => ⟨((-949078763/4398046511104), (182689809/1099511627776)), (615/549755813888), by norm_num⟩
  | 3 => ⟨((-908038293/8796093022208), (70865109/17592186044416)), (1829/2199023255552), by norm_num⟩
  | 4 => ⟨((-853769443/35184372088832), (-133654135/8796093022208)), (16579/35184372088832), by norm_num⟩
  | 5 => ⟨((-92121271/35184372088832), (-394111795/70368744177664)), (30431/140737488355328), by norm_num⟩
  | 6 => ⟨((128522449/1125899906842624), (-607703745/562949953421312)), (47087/562949953421312), by norm_num⟩
  | 7 => ⟨((825430669/9007199254740992), (-295861331/2251799813685248)), (126363/4503599627370496), by norm_num⟩
  | 8 => ⟨((646170943/36028797018963968), (-711268551/72057594037927936)), (37583/4503599627370496), by norm_num⟩
  | 9 => ⟨((669200427/288230376151711744), (-30342509/144115188075855872)), (1297929/576460752303423488), by norm_num⟩
  | 10 => ⟨((268231055/1152921504606846976), (156110681/2305843009213693952)), (2654637/4611686018427387904), by norm_num⟩
  | 11 => ⟨((347699511/18446744073709551616), (505922059/36893488147419103232)), (5872847/36893488147419103232), by norm_num⟩
  | 12 => ⟨((711615725/590295810358705651712), (502164421/295147905179352825856)), (1191059/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile036Gamma
