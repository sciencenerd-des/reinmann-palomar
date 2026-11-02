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
namespace Reinmann.XiRectangle.Tile042Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨42,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (3525/256))
  have he : value ((7/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((23/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((215/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((704512/11952005), (-72192/2390401)), 0, by norm_num⟩
  | 1 => ⟨((-183022518272/142850423520025), (50860130304/28570084704005)), 0, by norm_num⟩
  | 2 => ⟨((191388989/17592186044416), (-1263357779/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((429967403/562949953421312), (1283981371/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-512973755/9007199254740992), (-501592327/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((1452344593/576460752303423488), (450374127/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1587363779/18446744073709551616), (277033789/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 7 => ⟨((21300165/9223372036854775808), (-128538845/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-24649385/590295810358705651712), (50891953/590295810358705651712)), (13/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-21508357/302231454903657293676544), (-1917061949/604462909807314587353088)), (19/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((120864821/2417851639229258349412352), (893617989/9671406556917033397649408)), (7/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-887768325/309485009821345068724781056), (-609176631/309485009821345068724781056)), (41/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((565817591/4951760157141521099596496896), (145546649/9903520314283042199192993792)), (15/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((215/16), (3525/512)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((215/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((215/16), (3525/512)))⁻¹=value ((704512/11952005), (-72192/2390401)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((704512/11952005), (-72192/2390401))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1457389313/536870912), (254198933/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((352256/11952005), (-36096/2390401)), 0, by norm_num⟩
  | 2 => ⟨((-45755629568/142850423520025), (12715032576/28570084704005)), 0, by norm_num⟩
  | 3 => ⟨((255185319/140737488355328), (-1684477039/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((429967403/4503599627370496), (1283981371/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-102594751/18014398509481984), (-802547723/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((968229729/4611686018427387904), (150124709/2305843009213693952)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-1814130033/295147905179352825856), (316610045/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((21300165/147573952589676412928), (-128538845/1180591620717411303424)), (1/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-350569031/151115727451828646838272), (723796665/151115727451828646838272)), (3/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-34413371/9671406556917033397649408), (-1533649559/9671406556917033397649408)), (31/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((10987711/4835703278458516698824704), (81237999/19342813113834066795298816)), (41/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-295922775/2475880078570760549798248448), (-203058877/2475880078570760549798248448)), (55/9903520314283042199192993792), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-6959/276736), (75/8192)), 0, by norm_num⟩
  | 45 => ⟨((72831659629/3264510689280), (-296325/24117248)), 0, by norm_num⟩
  | 44 => ⟨((-193173054675349/9192862101012480), (438803750945/37933151158272)), 0, by norm_num⟩
  | 43 => ⟨((743669479/34359738368), (-187168973/17179869184)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-388057755/17179869184), (379951941/34359738368)), (1/17179869184), by norm_num⟩
  | 41 => ⟨((798849645/34359738368), (-394812515/34359738368)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-408523623/17179869184), (203487489/17179869184)), (1/17179869184), by norm_num⟩
  | 39 => ⟨((836753697/34359738368), (-416753261/34359738368)), (1/17179869184), by norm_num⟩
  | 38 => ⟨((-858886943/34359738368), (213399479/17179869184)), (1/17179869184), by norm_num⟩
  | 37 => ⟨((882547015/34359738368), (-437931727/34359738368)), (1/17179869184), by norm_num⟩
  | 36 => ⟨((-226835379/8589934592), (112473897/8589934592)), (1/17179869184), by norm_num⟩
  | 35 => ⟨((116679265/4294967296), (-462480695/34359738368)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-961071399/34359738368), (237861935/17179869184)), (1/17179869184), by norm_num⟩
  | 33 => ⟨((990422825/34359738368), (-489737109/34359738368)), (1/17179869184), by norm_num⟩
  | 32 => ⟨((-255407851/8589934592), (504611273/34359738368)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((1054866165/34359738368), (-520422447/34359738368)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-1090331361/34359738368), (4197309/268435456)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((1128262037/34359738368), (-555212077/34359738368)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-584462583/17179869184), (574409415/34359738368)), (1/17179869184), by norm_num⟩
  | 27 => ⟨((303156609/8589934592), (-594981245/34359738368)), (3/34359738368), by norm_num⟩
  | 26 => ⟨((-629859475/17179869184), (617080515/34359738368)), (1/17179869184), by norm_num⟩
  | 25 => ⟨((655306489/17179869184), (-640883659/34359738368)), (1/17179869184), by norm_num⟩
  | 24 => ⟨((-341446941/8589934592), (41662217/2147483648)), (1/17179869184), by norm_num⟩
  | 23 => ⟨((1425806515/34359738368), (-173613743/8589934592)), (1/17179869184), by norm_num⟩
  | 22 => ⟨((-93208477/2147483648), (5662053/268435456)), (1/17179869184), by norm_num⟩
  | 21 => ⟨((390792369/8589934592), (-189447651/8589934592)), (1/8589934592), by norm_num⟩
  | 20 => ⟨((-821131305/17179869184), (99249171/4294967296)), (1/8589934592), by norm_num⟩
  | 19 => ⟨((216221533/4294967296), (-416912537/17179869184)), (1/8589934592), by norm_num⟩
  | 18 => ⟨((-114194691/2147483648), (438929793/17179869184)), (1/8589934592), by norm_num⟩
  | 17 => ⟨((968021941/17179869184), (-463399191/17179869184)), (1/8589934592), by norm_num⟩
  | 16 => ⟨((-64336057/1073741824), (245377019/8589934592)), (1/8589934592), by norm_num⟩
  | 15 => ⟨((549507675/8589934592), (-1018625/33554432)), (1/8589934592), by norm_num⟩
  | 14 => ⟨((-589365935/8589934592), (278215597/8589934592)), (1/8589934592), by norm_num⟩
  | 13 => ⟨((19857477/268435456), (-596321725/17179869184)), (3/17179869184), by norm_num⟩
  | 12 => ⟨((-1378598947/17179869184), (642360951/17179869184)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((753095495/8589934592), (-348043143/8589934592)), (1/8589934592), by norm_num⟩
  | 10 => ⟨((-829844193/8589934592), (189898329/4294967296)), (1/8589934592), by norm_num⟩
  | 9 => ⟨((923916225/8589934592), (-208953491/4294967296)), (1/8589934592), by norm_num⟩
  | 8 => ⟨((-1041888305/8589934592), (232244791/4294967296)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((37316549/268435456), (-522713209/8589934592)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-349495177/2147483648), (597547175/8589934592)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((210594875/1073741824), (-348624505/4294967296)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((-529320895/2147483648), (209154241/2147483648)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((1421206623/4294967296), (-261263003/2147483648)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-1075128477/2147483648), (347613981/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((542523661/536870912), (-259149013/1073741824)), (1/1073741824), by norm_num⟩
  | 0 => ⟨((-124531693/2147483648), (1016795731/2147483648)), (1/1073741824), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-41/256), (3525/8192)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-41/256), (3525/8192)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-41/256), (3525/8192))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((1457389313/536870912), (254198933/536870912)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((215/16), (3525/512))) (z:=((-41/256), (3525/8192))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((1457389313/536870912), (254198933/536870912))) (r:=(1/268435456)) (by norm_num) ?_ hs
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
  | 0 => ⟨((207/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((1069054635/33554432), (832655159/33554432)), (3/33554432), by norm_num⟩
  | 1 => ⟨((989218637/536870912), (32788237/134217728)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1075419183104/142850423520025), (-114212409408/28570084704005)), 0, by norm_num⟩
  | 3 => ⟨((-477545863/8796093022208), (88135727/1099511627776)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((100719697/562949953421312), (-922487355/562949953421312)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((223284337/18014398509481984), (563751781/18014398509481984)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-41762545/72057594037927936), (-35785187/72057594037927936)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((666657259/36893488147419103232), (18972871/4611686018427387904)), (25/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-538733167/1180591620717411303424), (143421933/1180591620717411303424)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((693513621/75557863725914323419136), (-318988085/37778931862957161709568)), (23/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-552307107/4835703278458516698824704), (770743529/2417851639229258349412352)), (125/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-100415639/77371252455336267181195264), (-180041687/19342813113834066795298816)), (655/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((764731781/4951760157141521099596496896), (267399383/1237940039285380274899124224)), (437/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215/16), (-3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((618166955/33554432), (601640759/33554432)), (3/33554432), by norm_num⟩
  | 1 => ⟨((720783181/536870912), (32788237/134217728)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1075419183104/142850423520025), (-114212409408/28570084704005)), 0, by norm_num⟩
  | 3 => ⟨((-477545863/8796093022208), (88135727/1099511627776)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((100719697/562949953421312), (-922487355/562949953421312)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((223284337/18014398509481984), (563751781/18014398509481984)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-41762545/72057594037927936), (-35785187/72057594037927936)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((666657259/36893488147419103232), (18972871/4611686018427387904)), (25/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-538733167/1180591620717411303424), (143421933/1180591620717411303424)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((693513621/75557863725914323419136), (-318988085/37778931862957161709568)), (23/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-552307107/4835703278458516698824704), (770743529/2417851639229258349412352)), (125/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-100415639/77371252455336267181195264), (-180041687/19342813113834066795298816)), (655/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((764731781/4951760157141521099596496896), (267399383/1237940039285380274899124224)), (437/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((81125177/4194304), (601640759/33554432)), (1/8388608), by norm_num⟩
  | 1 => ⟨((720783181/536870912), (32788237/134217728)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1075419183104/142850423520025), (-114212409408/28570084704005)), 0, by norm_num⟩
  | 3 => ⟨((-477545863/8796093022208), (88135727/1099511627776)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((100719697/562949953421312), (-922487355/562949953421312)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((223284337/18014398509481984), (563751781/18014398509481984)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-41762545/72057594037927936), (-35785187/72057594037927936)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((666657259/36893488147419103232), (18972871/4611686018427387904)), (25/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-538733167/1180591620717411303424), (143421933/1180591620717411303424)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((693513621/75557863725914323419136), (-318988085/37778931862957161709568)), (23/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-552307107/4835703278458516698824704), (770743529/2417851639229258349412352)), (125/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-100415639/77371252455336267181195264), (-180041687/19342813113834066795298816)), (655/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((764731781/4951760157141521099596496896), (267399383/1237940039285380274899124224)), (437/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((366045036544/142850423520025), (-101720260608/28570084704005)), 0, by norm_num⟩
  | 1 => ⟨((-191388989/4398046511104), (1263357779/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-10077361/2199023255552), (-240746507/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((512973755/1125899906842624), (501592327/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-907715371/36028797018963968), (-281483829/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((595261417/576460752303423488), (-103887671/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-149101155/4611686018427387904), (899771915/36893488147419103232)), (5/18446744073709551616), by norm_num⟩
  | 7 => ⟨((24649385/36893488147419103232), (-50891953/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 8 => ⟨((24196901/18889465931478580854784), (1078347347/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-604324105/604462909807314587353088), (-139627811/75557863725914323419136)), (21/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((152585181/2417851639229258349412352), (837617869/19342813113834066795298816)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1697452775/618970019642690137449562112), (-109159987/309485009821345068724781056)), (47/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((28884359/309485009821345068724781056), (-332761221/9903520314283042199192993792)), (9/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((191388989/4398046511104), (-1263357779/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((10077361/1099511627776), (240746507/8796093022208)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-96182579/70368744177664), (-376194245/281474976710656)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((907715371/9007199254740992), (281483829/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1488153543/288230376151711744), (129859589/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 5 => ⟨((447303465/2305843009213693952), (-84353617/576460752303423488)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-690182781/147573952589676412928), (356243671/36893488147419103232)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-24196901/2361183241434822606848), (-1078347347/2361183241434822606848)), (5/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((339932309/37778931862957161709568), (1256650299/75557863725914323419136)), (17/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-762925905/1208925819614629174706176), (-4089931/9444732965739290427392)), (7/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1166998783/38685626227668133590597632), (75047491/19342813113834066795298816)), (23/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-1386449233/1237940039285380274899124224), (499141831/1237940039285380274899124224)), (35/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((622065693/19807040628566084398385987584), (-665409011/19807040628566084398385987584)), (27/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-429967403/70368744177664), (-1283981371/70368744177664)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((512973755/281474976710656), (501592327/281474976710656)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((-453857685/2251799813685248), (-281483829/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((496051181/36028797018963968), (-173146119/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((-745505775/1152921504606846976), (562357447/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((690182781/36893488147419103232), (-356243671/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((14114859/295147905179352825856), (1258071905/590295810358705651712)), (11/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-226621539/4722366482869645213696), (-418883433/4722366482869645213696)), (11/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1144388857/302231454903657293676544), (12269793/4722366482869645213696)), (19/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-486249493/2417851639229258349412352), (-7817447/302231454903657293676544)), (1/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((1270911797/154742504910672534362390528), (-228773339/77371252455336267181195264)), (27/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-622065693/2475880078570760549798248448), (665409011/2475880078570760549798248448)), (11/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((331436791/79228162514264337593543950336), (-145023673/9903520314283042199192993792)), (17/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-512973755/562949953421312), (-501592327/562949953421312)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((907715371/4503599627370496), (281483829/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 2 => ⟨((-744076771/36028797018963968), (129859589/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((745505775/576460752303423488), (-562357447/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((-215682119/4611686018427387904), (445304589/4611686018427387904)), (9/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-42344577/295147905179352825856), (-1887107857/295147905179352825856)), (9/147573952589676412928), by norm_num⟩
  | 6 => ⟨((198293847/1180591620717411303424), (91630751/295147905179352825856)), (5/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-1144388857/75557863725914323419136), (-785266753/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((1094061359/1208925819614629174706176), (70357023/604462909807314587353088)), (17/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-794319873/19342813113834066795298816), (142983337/9671406556917033397649408)), (1/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((106917541/77371252455336267181195264), (-457468695/309485009821345068724781056)), (27/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-248577593/9903520314283042199192993792), (435071019/4951760157141521099596496896)), (23/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-248033047/316912650057057350374175801344), (-313588479/79228162514264337593543950336)), (19/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1452344593/18014398509481984), (-450374127/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 1 => ⟨((595261417/36028797018963968), (-207775343/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 2 => ⟨((-894606929/576460752303423488), (84353617/72057594037927936)), (9/576460752303423488), by norm_num⟩
  | 3 => ⟨((172545695/2305843009213693952), (-356243671/2305843009213693952)), (17/9223372036854775808), by norm_num⟩
  | 4 => ⟨((42344577/147573952589676412928), (1887107857/147573952589676412928)), (23/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-475905233/1180591620717411303424), (-879655209/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((100134025/2361183241434822606848), (549686727/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-1750498175/604462909807314587353088), (-112571237/302231454903657293676544)), (29/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((1429775771/9671406556917033397649408), (-514740013/9671406556917033397649408)), (29/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-106917541/19342813113834066795298816), (914937391/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((34179419/309485009821345068724781056), (-478578121/1237940039285380274899124224)), (25/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((297639657/79228162514264337593543950336), (1505224699/79228162514264337593543950336)), (11/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-89254777/158456325028528675187087900672), (-451841023/633825300114114700748351602688)), (37/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1587363779/288230376151711744), (277033789/288230376151711744)), (5/144115188075855872), by norm_num⟩
  | 1 => ⟨((1192809239/1152921504606846976), (-899771915/1152921504606846976)), (15/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-172545695/2305843009213693952), (356243671/2305843009213693952)), (9/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-14114859/36893488147419103232), (-39314747/2305843009213693952)), (9/36893488147419103232), by norm_num⟩
  | 4 => ⟨((198293847/295147905179352825856), (733046007/590295810358705651712)), (7/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-100134025/1180591620717411303424), (-274843363/4722366482869645213696)), (17/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1021123935/151115727451828646838272), (131333109/151115727451828646838272)), (21/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-119147981/302231454903657293676544), (343160009/2417851639229258349412352)), (11/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((320752623/19342813113834066795298816), (-686203043/38685626227668133590597632)), (11/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-455725587/1237940039285380274899124224), (1595260403/1237940039285380274899124224)), (11/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-1065767/77371252455336267181195264), (-344947327/4951760157141521099596496896)), (21/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((89254777/39614081257132168796771975168), (451841023/158456325028528675187087900672)), (39/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-416285751/2535301200456458802993406410752), (-380437201/5070602400912917605986812821504)), (35/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-21300165/72057594037927936), (128538845/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((24649385/576460752303423488), (-50891953/576460752303423488)), (3/2305843009213693952), by norm_num⟩
  | 2 => ⟨((24196901/73786976294838206464), (1078347347/73786976294838206464)), (17/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-226621539/295147905179352825856), (-837766865/590295810358705651712)), (9/295147905179352825856), by norm_num⟩
  | 4 => ⟨((1144388857/9444732965739290427392), (785266751/9444732965739290427392)), (15/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-875249087/75557863725914323419136), (-28142809/18889465931478580854784)), (41/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((953183847/1208925819614629174706176), (-343160009/1208925819614629174706176)), (13/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-183287213/4835703278458516698824704), (784232049/19342813113834066795298816)), (31/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((292966449/309485009821345068724781056), (-1025524545/309485009821345068724781056)), (1/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((194883109/4951760157141521099596496896), (985563791/4951760157141521099596496896)), (33/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-561030027/79228162514264337593543950336), (-710035893/79228162514264337593543950336)), (33/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((1427265433/2535301200456458802993406410752), (163044515/633825300114114700748351602688)), (63/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-657568347/20282409603651670423947251286016), (59050107/40564819207303340847894502572032)), (59/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-24649385/2305843009213693952), (50891953/2305843009213693952)), (13/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-24196901/147573952589676412928), (-1078347347/147573952589676412928)), (5/36893488147419103232), by norm_num⟩
  | 2 => ⟨((339932309/590295810358705651712), (1256650299/1180591620717411303424)), (15/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-143048607/1180591620717411303424), (-12269793/147573952589676412928)), (35/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((547030679/37778931862957161709568), (140714045/75557863725914323419136)), (31/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-714887885/604462909807314587353088), (257370007/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((641505245/9671406556917033397649408), (-686203043/9671406556917033397649408)), (1/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-18310403/9671406556917033397649408), (1025524545/154742504910672534362390528)), (39/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((-219243497/2475880078570760549798248448), (-1108759265/2475880078570760549798248448)), (11/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((350643767/19807040628566084398385987584), (443772433/19807040628566084398385987584)), (47/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-981244985/633825300114114700748351602688), (-7005819/9903520314283042199192993792)), (49/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((986352521/10141204801825835211973625643008), (-88575161/20282409603651670423947251286016)), (97/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-757374897/162259276829213363391578010288128), (431988817/162259276829213363391578010288128)), (3/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21508357/590295810358705651712), (1917061949/1180591620717411303424)), (19/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-604324105/2361183241434822606848), (-139627811/295147905179352825856)), (1/73786976294838206464), by norm_num⟩
  | 2 => ⟨((762925905/9444732965739290427392), (4089931/73786976294838206464)), (13/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-972498985/75557863725914323419136), (-7817447/4722366482869645213696)), (33/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((775703/590295810358705651712), (-142983337/302231454903657293676544)), (31/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-855340327/9671406556917033397649408), (457468695/4835703278458516698824704)), (25/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((455725585/154742504910672534362390528), (-797630201/77371252455336267181195264)), (73/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((194883109/1237940039285380274899124224), (985563791/1237940039285380274899124224)), (3/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-350643767/9903520314283042199192993792), (-443772433/9903520314283042199192993792)), (57/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((1090272205/316912650057057350374175801344), (498191573/316912650057057350374175801344)), (1/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-602770985/2535301200456458802993406410752), (54129265/5070602400912917605986812821504)), (69/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((1009833197/81129638414606681695789005144064), (-287992545/40564819207303340847894502572032)), (9/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-294906519/649037107316853453566312041152512), (902289547/1298074214633706907132624082305024)), (9/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((120864821/2361183241434822606848), (893617989/9444732965739290427392)), (7/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((-152585181/4722366482869645213696), (-837617869/37778931862957161709568)), (25/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((1166998783/151115727451828646838272), (75047491/75557863725914323419136)), (11/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-317727949/302231454903657293676544), (228773339/604462909807314587353088)), (15/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((855340327/9671406556917033397649408), (-457468695/4835703278458516698824704)), (61/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-34179419/9671406556917033397649408), (957156241/77371252455336267181195264)), (13/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-272836353/1237940039285380274899124224), (-689894653/618970019642690137449562112)), (5/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((561030027/9903520314283042199192993792), (710035893/9903520314283042199192993792)), (7/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-981244985/158456325028528675187087900672), (-448372415/158456325028528675187087900672)), (71/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((1205541969/2535301200456458802993406410752), (-54129265/2535301200456458802993406410752)), (83/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-277704129/10141204801825835211973625643008), (633583599/40564819207303340847894502572032)), (93/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((353887823/324518553658426726783156020576256), (-16917929/10141204801825835211973625643008)), (101/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-66147175/5192296858534827628530496329220096), (624785549/5192296858534827628530496329220096)), (105/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((176128/35856015), (-6016/2390401)), 0, by norm_num⟩
  | 1 => ⟨((-45755629568/428551270560075), (4238344192/28570084704005)), 0, by norm_num⟩
  | 2 => ⟨((255185319/281474976710656), (-1684477039/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((286644935/4503599627370496), (855987581/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-683965007/144115188075855872), (-668789769/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((968229729/4611686018427387904), (150124709/2305843009213693952)), (5/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-1058242519/147573952589676412928), (184689193/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((7100055/36893488147419103232), (-685540507/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-525853547/151115727451828646838272), (1085694997/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-28677809/4835703278458516698824704), (-1278041299/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((644612379/154742504910672534362390528), (297872663/38685626227668133590597632)), (19/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-295922775/1237940039285380274899124224), (-203058877/1237940039285380274899124224)), (55/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((1508846909/158456325028528675187087900672), (194062199/158456325028528675187087900672)), (81/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((324583119/16777216), (601556311/33554432)), (5/33554432), by norm_num⟩
  | 1 => ⟨((1441451721/1073741824), (262465185/1073741824)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((517402339/68719476736), (-137562883/34359738368)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-238493005/4398046511104), (706757667/8796093022208)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((196095917/1125899906842624), (-925099815/562949953421312)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((454132969/36028797018963968), (1129849261/36028797018963968)), (15/18014398509481984), by norm_num⟩
  | 6 => ⟨((-42279265/72057594037927936), (-142780027/288230376151711744)), (43/1152921504606846976), by norm_num⟩
  | 7 => ⟨((336878657/18446744073709551616), (146427183/36893488147419103232)), (101/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-271420699/590295810358705651712), (151903925/1180591620717411303424)), (129/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((346532765/37778931862957161709568), (-657945565/75557863725914323419136)), (185/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-266081485/2417851639229258349412352), (1578721141/4835703278458516698824704)), (251/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-237821625/154742504910672534362390528), (-91607241/9671406556917033397649408)), (329/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((811883247/4951760157141521099596496896), (134457747/618970019642690137449562112)), (877/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-272197673/2251799813685248), (449193877/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-57328987/2251799813685248), (-1369580129/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((547172005/144115188075855872), (535031815/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-322743243/1152921504606846976), (-400332557/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 4 => ⟨((1058242519/73786976294838206464), (-184689193/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-9940077/18446744073709551616), (239939177/590295810358705651712)), (3/590295810358705651712), by norm_num⟩
  | 6 => ⟨((122699161/9444732965739290427392), (-1013315331/37778931862957161709568)), (9/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((17206685/604462909807314587353088), (191706195/151115727451828646838272)), (15/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-120864821/4835703278458516698824704), (-446808995/9671406556917033397649408)), (13/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((16953909/9671406556917033397649408), (744549217/618970019642690137449562112)), (21/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-829865801/9903520314283042199192993792), (-213468419/19807040628566084398385987584)), (17/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((985919455/316912650057057350374175801344), (-177472651/158456325028528675187087900672)), (13/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-221178913/2535301200456458802993406410752), (473179741/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((324583117/16777216), (300778169/16777216)), (3/16777216), by norm_num⟩
  | 1 => ⟨((720725847/536870912), (262465103/1073741824)), (3/536870912), by norm_num⟩
  | 2 => ⟨((64675325/8589934592), (-275125511/68719476736)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-59623559/1099511627776), (706756903/8796093022208)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((3064251/17592186044416), (-115637653/70368744177664)), (21/1125899906842624), by norm_num⟩
  | 5 => ⟨((454113555/36028797018963968), (564931953/18014398509481984)), (31/36028797018963968), by norm_num⟩
  | 6 => ⟨((-338226631/576460752303423488), (-71393879/144115188075855872)), (11/288230376151711744), by norm_num⟩
  | 7 => ⟨((168439591/9223372036854775808), (292947973/73786976294838206464)), (51/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-271435453/590295810358705651712), (151849383/1180591620717411303424)), (65/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((346598991/37778931862957161709568), (-328927339/37778931862957161709568)), (93/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-266284089/2417851639229258349412352), (1578669025/4835703278458516698824704)), (503/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-237340219/154742504910672534362390528), (-1465889169/154742504910672534362390528)), (659/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((811451257/4951760157141521099596496896), (538062033/2475880078570760549798248448)), (439/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-833785913/1152921504606846976), (-50955411/72057594037927936)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((737698841/4611686018427387904), (228761461/4611686018427387904)), (9/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-1209420021/73786976294838206464), (52768341/18446744073709551616)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((2366685/2305843009213693952), (-914054009/1180591620717411303424)), (7/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-43821129/1180591620717411303424), (723796665/9444732965739290427392)), (9/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-34413371/302231454903657293676544), (-191706195/37778931862957161709568)), (1/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((644612379/4835703278458516698824704), (595745327/2417851639229258349412352)), (17/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-7265961/604462909807314587353088), (-159546261/19342813113834066795298816)), (17/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((444570965/618970019642690137449562112), (57179041/618970019642690137449562112)), (29/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-161385625/4951760157141521099596496896), (116202331/9903520314283042199192993792)), (27/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((695133727/633825300114114700748351602688), (-743568165/633825300114114700748351602688)), (23/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-404037231/20282409603651670423947251286016), (707163053/10141204801825835211973625643008)), (39/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-1574813/2535301200456458802993406410752), (-254852859/81129638414606681695789005144064)), (1/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((324583117/16777216), (300778169/16777216)), (7/33554432), by norm_num⟩
  | 1 => ⟨((720725847/536870912), (262465103/1073741824)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((517402599/68719476736), (-275125511/68719476736)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-476988463/8796093022208), (22086153/274877906944)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((98056011/562949953421312), (-925101181/562949953421312)), (11/562949953421312), by norm_num⟩
  | 5 => ⟨((454113551/36028797018963968), (1129863723/36028797018963968)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-169113277/288230376151711744), (-142787687/288230376151711744)), (45/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1347515841/73786976294838206464), (73236841/18446744073709551616)), (103/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-271435029/590295810358705651712), (37962373/295147905179352825856)), (131/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((693195519/75557863725914323419136), (-657853791/75557863725914323419136)), (187/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-532562875/4835703278458516698824704), (197332919/604462909807314587353088)), (63/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-118671651/77371252455336267181195264), (-1465878379/154742504910672534362390528)), (165/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((811448181/4951760157141521099596496896), (1076108511/4951760157141521099596496896)), (879/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((483768009/147573952589676412928), (-84429345/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-727045631/1180591620717411303424), (548432405/1180591620717411303424)), (5/590295810358705651712), by norm_num⟩
  | 2 => ⟨((420682837/9444732965739290427392), (-434277999/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((34413371/151115727451828646838272), (1533649559/151115727451828646838272)), (23/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-120864821/302231454903657293676544), (-893617989/1208925819614629174706176)), (9/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((488272579/9671406556917033397649408), (670094295/19342813113834066795298816)), (11/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((-622399351/154742504910672534362390528), (-80050657/154742504910672534362390528)), (27/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((290494125/1237940039285380274899124224), (-52291049/618970019642690137449562112)), (7/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-782025443/79228162514264337593543950336), (418257093/39614081257132168796771975168)), (7/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((69443899/316912650057057350374175801344), (-486174599/633825300114114700748351602688)), (27/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((332600505/40564819207303340847894502572032), (1682028871/40564819207303340847894502572032)), (13/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((-870446587/649037107316853453566312041152512), (-1101631447/649037107316853453566312041152512)), (49/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((1014944307/10384593717069655257060992658440192), (57971383/1298074214633706907132624082305024)), (43/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((324583117/16777216), (300778169/16777216)), (1/4194304), by norm_num⟩
  | 1 => ⟨((720725847/536870912), (262465103/1073741824)), (1/134217728), by norm_num⟩
  | 2 => ⟨((517402599/68719476736), (-275125511/68719476736)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-476988463/8796093022208), (22086153/274877906944)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((98056011/562949953421312), (-1850202363/1125899906842624)), (23/1125899906842624), by norm_num⟩
  | 5 => ⟨((454113553/36028797018963968), (282465931/9007199254740992)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-676453113/1152921504606846976), (-571150749/1152921504606846976)), (23/576460752303423488), by norm_num⟩
  | 7 => ⟨((673757929/36893488147419103232), (146473679/36893488147419103232)), (13/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-1085740139/2361183241434822606848), (303699009/2361183241434822606848)), (33/590295810358705651712), by norm_num⟩
  | 9 => ⟨((43324721/4722366482869645213696), (-657853849/75557863725914323419136)), (47/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-532562835/4835703278458516698824704), (1578663553/4835703278458516698824704)), (505/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-118671755/77371252455336267181195264), (-732939321/77371252455336267181195264)), (661/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((811448665/4951760157141521099596496896), (269027183/1237940039285380274899124224)), (55/309485009821345068724781056), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-339945727/37778931862957161709568), (1403726865/75557863725914323419136)), (23/75557863725914323419136), by norm_num⟩
  | 1 => ⟨((-5214147/37778931862957161709568), (-464742291/75557863725914323419136)), (35/302231454903657293676544), by norm_num⟩
  | 2 => ⟨((586011253/1208925819614629174706176), (541586661/604462909807314587353088)), (27/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((-493204625/4835703278458516698824704), (-169215731/2417851639229258349412352)), (31/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((1886058637/154742504910672534362390528), (60644437/38685626227668133590597632)), (55/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-1232399317/1237940039285380274899124224), (110920407/309485009821345068724781056)), (5/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((276473641/4951760157141521099596496896), (-591474677/9903520314283042199192993792)), (7/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((-63130817/39614081257132168796771975168), (883953817/158456325028528675187087900672)), (35/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((-23622195/316912650057057350374175801344), (-477849111/1267650600228229401496703205376)), (39/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((604476797/40564819207303340847894502572032), (765021837/40564819207303340847894502572032)), (41/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-845786923/649037107316853453566312041152512), (-386475887/649037107316853453566312041152512)), (43/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((1700378757/20769187434139310514121985316880384), (-38173807/10384593717069655257060992658440192)), (85/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((-163205365/41538374868278621028243970633760768), (372353997/166153499473114484112975882535043072)), (21/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((324583117/16777216), (300778169/16777216)), (9/33554432), by norm_num⟩
  | 1 => ⟨((720725847/536870912), (262465103/1073741824)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((517402599/68719476736), (-275125511/68719476736)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-476988463/8796093022208), (22086153/274877906944)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((98056011/562949953421312), (-1850202363/1125899906842624)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((454113553/36028797018963968), (282465931/9007199254740992)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-676453113/1152921504606846976), (-571150749/1152921504606846976)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((673757929/36893488147419103232), (146473679/36893488147419103232)), (105/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1085740139/2361183241434822606848), (4745297/36893488147419103232)), (133/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((693195537/75557863725914323419136), (-82231731/9444732965739290427392)), (189/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-532562841/4835703278458516698824704), (789331775/2417851639229258349412352)), (253/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-237343497/154742504910672534362390528), (-1465878643/154742504910672534362390528)), (331/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((405724323/2475880078570760549798248448), (1076108743/4951760157141521099596496896)), (881/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-237323825/2417851639229258349412352), (-877330713/4835703278458516698824704)), (29/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((599216521/9671406556917033397649408), (822351263/19342813113834066795298816)), (25/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((-1145728809/77371252455336267181195264), (-73679659/38685626227668133590597632)), (11/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((155968485/77371252455336267181195264), (-112301833/154742504910672534362390528)), (15/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((-209937677/1237940039285380274899124224), (898261541/4951760157141521099596496896)), (61/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((67112915/9903520314283042199192993792), (-469855451/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 6 => ⟨((133931789/316912650057057350374175801344), (1354640965/633825300114114700748351602688)), (79/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-550804571/5070602400912917605986812821504), (-21784207/158456325028528675187087900672)), (7/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((120420075/10141204801825835211973625643008), (220100141/40564819207303340847894502572032)), (71/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((-591784749/649037107316853453566312041152512), (53142693/1298074214633706907132624082305024)), (41/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((272642633/5192296858534827628530496329220096), (-311017883/10384593717069655257060992658440192)), (23/5192296858534827628530496329220096), by norm_num⟩
  | 11 => ⟨((-694875573/332306998946228968225951765070086144), (1063013065/332306998946228968225951765070086144)), (25/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((32470781/1329227995784915872903807060280344576), (-613398071/2658455991569831745807614120560689152)), (13/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((324583117/16777216), (300778169/16777216)), (5/16777216), by norm_num⟩
  | 1 => ⟨((720725847/536870912), (262465103/1073741824)), (5/536870912), by norm_num⟩
  | 2 => ⟨((517402599/68719476736), (-275125511/68719476736)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-476988463/8796093022208), (22086153/274877906944)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((98056011/562949953421312), (-1850202363/1125899906842624)), (25/1125899906842624), by norm_num⟩
  | 5 => ⟨((454113553/36028797018963968), (282465931/9007199254740992)), (35/36028797018963968), by norm_num⟩
  | 6 => ⟨((-676453113/1152921504606846976), (-571150749/1152921504606846976)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((673757929/36893488147419103232), (146473679/36893488147419103232)), (53/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1085740139/2361183241434822606848), (4745297/36893488147419103232)), (67/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((693195537/75557863725914323419136), (-82231731/9444732965739290427392)), (95/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-532562841/4835703278458516698824704), (789331775/2417851639229258349412352)), (507/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-237343497/154742504910672534362390528), (-1465878643/154742504910672534362390528)), (663/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((405724323/2475880078570760549798248448), (538054371/2475880078570760549798248448)), (441/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2499740077095/16384), (-26359758542965/131072)), (629564057/4194304), by norm_num⟩
  | 1 => ⟨((1015921307/4), (-930741701/4)), (967/4), by norm_num⟩
  | 2 => ⟨(199261130, (-509074497/4)), 196, by norm_num⟩
  | 3 => ⟨((801583823/8), (-340302173/8)), (427/4), by norm_num⟩
  | 4 => ⟨((587617551/16), (-288214413/32)), (351/8), by norm_num⟩
  | 5 => ⟨((1348350591/128), (-57468539/64)), (465/32), by norm_num⟩
  | 6 => ⟨((316482989/128), (10341025/64)), (517/128), by norm_num⟩
  | 7 => ⟨((1002704113/2048), (214477803/2048)), (1987/2048), by norm_num⟩
  | 8 => ⟨((1369450349/16384), (502483003/16384)), (1685/8192), by norm_num⟩
  | 9 => ⟨((819102889/65536), (435194705/65536)), (2561/65536), by norm_num⟩
  | 10 => ⟨((434065445/262144), (621212069/524288)), (3533/524288), by norm_num⟩
  | 11 => ⟨((205402979/1048576), (382765439/2097152)), (1117/1048576), by norm_num⟩
  | 12 => ⟨((348701985/16777216), (208993259/8388608)), (5223/33554432), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1609176953630357/10141204801825835211973625643008), (-1200721370009/10141204801825835211973625643008)), (388209/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((906187098897031/316912650057057350374175801344), (-735613811263/316912650057057350374175801344)), (238183/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((481896575367051/9903520314283042199192993792), (-829625798091/19807040628566084398385987584)), (537329/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1929762860297251/2475880078570760549798248448), (-883257560453/1237940039285380274899124224)), (572121/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1811469758822373/154742504910672534362390528), (-432251211/37778931862957161709568)), (286737/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1587358328795889/9671406556917033397649408), (-1664091680333/9671406556917033397649408)), (269537/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1291911346141825/604462909807314587353088), (-1460341583899/604462909807314587353088)), (473137/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1941697903239865/75557863725914323419136), (-2381075737299/75557863725914323419136)), (192893/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1338040396674839/4722366482869645213696), (-1792855628281/4722366482869645213696)), (290537/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((209656696799711/73786976294838206464), (-619172192587/147573952589676412928)), (401445/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1893407130400041/73786976294838206464), (-3113231371755/73786976294838206464)), (1009517/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1901573659508905/9223372036854775808), (-1763218224427/4611686018427387904)), (1143885/9223372036854775808), by norm_num⟩
  | 6 => ⟨((836563616467571/576460752303423488), (-3556752624499/1152921504606846976)), (577099/576460752303423488), by norm_num⟩
  | 5 => ⟨((1264175032453731/144115188075855872), (-3146614283127/144115188075855872)), (1021651/144115188075855872), by norm_num⟩
  | 4 => ⟨((798362957041627/18014398509481984), (-4789717754409/36028797018963968)), (1556245/36028797018963968), by norm_num⟩
  | 3 => ⟨((1621851830964257/9007199254740992), (-6111308843679/9007199254740992)), (248453/1125899906842624), by norm_num⟩
  | 2 => ⟨((312111485416039/562949953421312), (-6301656277327/2251799813685248)), (2052567/2251799813685248), by norm_num⟩
  | 1 => ⟨((1314551876803201/1125899906842624), (-9943035257165/1125899906842624)), (405807/140737488355328), by norm_num⟩
  | 0 => ⟨((380783667130813/281474976710656), (-21938940125937/1125899906842624)), (1798949/281474976710656), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((380783667130813/281474976710656), (-21938940125937/1125899906842624)), (6862445832372569949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((64377889168565/35184372088832), (-59358669617763/1125899906842624)), (9874799/562949953421312), by norm_num⟩
  | 2 => ⟨((941570702489003/281474976710656), (-54305159179731/281474976710656)), (37177647/562949953421312), by norm_num⟩
  | 3 => ⟨((98100010056623/8796093022208), (-181657877638615/140737488355328)), (8221051/17592186044416), by norm_num⟩
  | 4 => ⟨((1079423253273093/8796093022208), (-253246520617451/8796093022208)), (102298131/8796093022208), by norm_num⟩
  | 5 => ⟨((977902878231361/68719476736), (-242792615492409/34359738368)), (60542519/17179869184), by norm_num⟩
  | 6 => ⟨((2499740077095/16384), (-26359758542965/131072)), (629564057/4194304), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((324583117/16777216), (300778169/16777216)), (5/16777216), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((376832/12967321), (-1804800/12967321)), 0, by norm_num⟩
  | 1 => ⟨((1557650341888/168151413917041), (680106393600/168151413917041)), 0, by norm_num⟩
  | 2 => ⟨((-228733045/549755813888), (322087157/549755813888)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-610900549/17592186044416), (-164780419/4398046511104)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((875918581/281474976710656), (-526970943/281474976710656)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((383118769/4503599627370496), (137224749/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-655702817/36028797018963968), (171364519/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((114071935/1152921504606846976), (-1500017173/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 8 => ⟨((205458401/2305843009213693952), (237869179/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-455914985/147573952589676412928), (859766529/147573952589676412928)), (7/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-851311247/2361183241434822606848), (-88439463/295147905179352825856)), (5/590295810358705651712), by norm_num⟩
  | 11 => ⟨((492846799/18889465931478580854784), (-783404363/37778931862957161709568)), (7/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((80390337/75557863725914323419136), (1279642349/604462909807314587353088)), (39/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((23/16), (3525/512)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((23/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((23/16), (3525/512)))⁻¹=value ((376832/12967321), (-1804800/12967321)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((376832/12967321), (-1804800/12967321))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((212992/4661043), (-601600/4661043)), 0, by norm_num⟩
  | 1 => ⟨((52759494656/7241773949283), (128135987200/21725321847849)), 0, by norm_num⟩
  | 2 => ⟨((-1203053689/2199023255552), (737567643/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-321781855/35184372088832), (-1511855791/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((839356689/281474976710656), (220430019/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((-105161703/1125899906842624), (25824803/140737488355328)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-699524191/72057594037927936), (-46027935/4503599627370496)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((1016149471/1152921504606846976), (-226538517/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((96355147/18446744073709551616), (607432547/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-161205489/36893488147419103232), (-344625509/295147905179352825856)), (13/147573952589676412928), by norm_num⟩
  | 10 => ⟨((827300743/4722366482869645213696), (-1205648265/4722366482869645213696)), (19/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((117808301/9444732965739290427392), (647492471/37778931862957161709568)), (27/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-420421243/302231454903657293676544), (124936139/302231454903657293676544)), (39/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((39/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((39/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((39/16), (3525/512)))⁻¹=value ((212992/4661043), (-601600/4661043)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((212992/4661043), (-601600/4661043))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1005505478656/60441240775803), (-611110092800/60441240775803)), 0, by norm_num⟩
  | 1 => ⟨((1087384813/549755813888), (-1018914537/549755813888)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((72030377/549755813888), (1101561967/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-450009621/17592186044416), (96806219/17592186044416)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((73123785/562949953421312), (-1274371903/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((803765579/4503599627370496), (33925537/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-152970361/18014398509481984), (907811477/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((-902077535/1152921504606846976), (-523470069/576460752303423488)), (15/1152921504606846976), by norm_num⟩
  | 8 => ⟨((386828015/4611686018427387904), (-46195421/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 9 => ⟨((188906971/147573952589676412928), (516039641/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-1264961617/2361183241434822606848), (-104691571/2361183241434822606848)), (27/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((257230197/18889465931478580854784), (-1430896833/37778931862957161709568)), (5/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((370991295/151115727451828646838272), (514885035/302231454903657293676544)), (15/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((55/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((180224/3104645), (-72192/620929)), 0, by norm_num⟩
  | 1 => ⟨((48905715712/9638820576025), (13010731008/1927764115205)), 0, by norm_num⟩
  | 2 => ⟨((-1186613735/2199023255552), (217835729/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((348448957/35184372088832), (-1204850977/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((958832057/562949953421312), (883628751/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-1267157263/9007199254740992), (481469311/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((4395107/4503599627370496), (-1402196801/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((1238891111/2305843009213693952), (781992573/2305843009213693952)), (15/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-1302682789/36893488147419103232), (98644549/4611686018427387904)), (11/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-64521629/295147905179352825856), (-197266129/73786976294838206464)), (31/590295810358705651712), by norm_num⟩
  | 10 => ⟨((95485659/590295810358705651712), (612855311/9444732965739290427392)), (11/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-319880161/37778931862957161709568), (142049355/18889465931478580854784)), (1/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-231385879/1208925819614629174706176), (-858921255/1208925819614629174706176)), (23/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((55/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((55/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((55/16), (3525/512)))⁻¹=value ((180224/3104645), (-72192/620929)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((180224/3104645), (-72192/620929))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-588582263/274877906944), (740661395/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((-256921445/2199023255552), (-1102003493/2199023255552)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((152280731/2199023255552), (124196277/17592186044416)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-114894215/35184372088832), (1001234505/140737488355328)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-20211173/35184372088832), (-611173171/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((1181667519/18014398509481984), (-314254743/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 6 => ⟨((157964459/144115188075855872), (235790009/36028797018963968)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((-1298781449/2305843009213693952), (-202866817/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((399807759/18446744073709551616), (-12182919/288230376151711744)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((50091757/18446744073709551616), (404929889/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-162083669/590295810358705651712), (651346389/4722366482869645213696)), (35/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-69163243/18889465931478580854784), (-1794290593/75557863725914323419136)), (53/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1104557363/604462909807314587353088), (87609291/302231454903657293676544)), (41/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((71/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((1163264/17587609), (-1804800/17587609)), 0, by norm_num⟩
  | 1 => ⟨((952059953152/309323990336881), (2099458867200/309323990336881)), 0, by norm_num⟩
  | 2 => ⟨((-494816407/1099511627776), (-9144633/137438953472)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((321879333/17592186044416), (-735011721/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((65692599/140737488355328), (917404209/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-892174693/9007199254740992), (-134852959/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((693488213/144115188075855872), (-294857067/72057594037927936)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((234352443/4611686018427387904), (1762696225/4611686018427387904)), (25/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-196384165/9223372036854775808), (-370151911/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 9 => ⟨((179880811/147573952589676412928), (-449021659/590295810358705651712)), (25/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-3024993/2361183241434822606848), (1656553799/18889465931478580854784)), (69/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-168391131/37778931862957161709568), (-224099303/75557863725914323419136)), (3/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((181086833/604462909807314587353088), (-631604625/4835703278458516698824704)), (131/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((71/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((71/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((71/16), (3525/512)))⁻¹=value ((1163264/17587609), (-1804800/17587609)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((1163264/17587609), (-1804800/17587609))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-14832001/4398046511104), (1358288679/4398046511104)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-658715995/8796093022208), (-138726469/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((661442643/70368744177664), (-664175935/70368744177664)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((96755115/140737488355328), (225188541/140737488355328)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((-894102929/4503599627370496), (12166735/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((126940437/18014398509481984), (-349550779/18014398509481984)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((868517289/576460752303423488), (763023015/576460752303423488)), (7/288230376151711744), by norm_num⟩
  | 7 => ⟨((-756418613/4611686018427387904), (394352489/4611686018427387904)), (13/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-8610587/4611686018427387904), (-600015459/36893488147419103232)), (23/73786976294838206464), by norm_num⟩
  | 9 => ⟨((400629209/295147905179352825856), (203575621/590295810358705651712)), (39/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-628939639/9444732965739290427392), (451176317/4722366482869645213696)), (1/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-812836911/151115727451828646838272), (-1174357327/151115727451828646838272)), (51/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((219790375/302231454903657293676544), (-226468597/1208925819614629174706176)), (5/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((87/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((475136/6725427), (-601600/6725427)), 0, by norm_num⟩
  | 1 => ⟨((22694723584/15077122777443), (285841817600/45231368332329)), 0, by norm_num⟩
  | 2 => ⟨((-738470971/2199023255552), (-342844561/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((331357061/17592186044416), (-41836205/4398046511104)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-270091519/1125899906842624), (1326813985/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((-796833973/18014398509481984), (-943171813/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 6 => ⟨((1125301539/288230376151711744), (-4645123/36028797018963968)), (5/144115188075855872), by norm_num⟩
  | 7 => ⟨((-304703463/2305843009213693952), (103285327/576460752303423488)), (7/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-61718149/18446744073709551616), (-225774757/18446744073709551616)), (19/73786976294838206464), by norm_num⟩
  | 9 => ⟨((785796867/1180591620717411303424), (333749879/1180591620717411303424)), (25/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-341476791/9444732965739290427392), (373696793/18889465931478580854784)), (65/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((237141445/604462909807314587353088), (-174984183/75557863725914323419136)), (21/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((867739031/9671406556917033397649408), (240221051/2417851639229258349412352)), (109/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((87/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((87/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((87/16), (3525/512)))⁻¹=value ((475136/6725427), (-601600/6725427)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((475136/6725427), (-601600/6725427))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((963625657/35184372088832), (778293817/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-708540553/70368744177664), (691574555/140737488355328)), (7/140737488355328), by norm_num⟩
  | 2 => ⟨((-12477591/281474976710656), (-1199953289/562949953421312)), (7/562949953421312), by norm_num⟩
  | 3 => ⟨((324932695/1125899906842624), (562299709/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 4 => ⟨((-132050451/4503599627370496), (959735203/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 5 => ⟨((-200833173/144115188075855872), (-1225999931/288230376151711744)), (15/288230376151711744), by norm_num⟩
  | 6 => ⟨((133828393/288230376151711744), (107599967/2305843009213693952)), (17/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-413704525/18446744073709551616), (734762075/18446744073709551616)), (17/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-380148859/147573952589676412928), (-500574591/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | 9 => ⟨((436169771/1180591620717411303424), (-109145203/1180591620717411303424)), (27/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-95842047/18889465931478580854784), (613832997/18889465931478580854784)), (45/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-710044773/302231454903657293676544), (-109006289/75557863725914323419136)), (37/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((220185113/1208925819614629174706176), (-640250985/4835703278458516698824704)), (59/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((103/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((1687552/23289241), (-1804800/23289241)), 0, by norm_num⟩
  | 1 => ⟨((204735643648/542388746356081), (3045693849600/542388746356081)), 0, by norm_num⟩
  | 2 => ⟨((-127134351/549755813888), (-830435401/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1104419483/70368744177664), (-9322195/4398046511104)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-273872411/562949953421312), (771158941/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-321136983/36028797018963968), (-786608947/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((1161490497/576460752303423488), (712878183/576460752303423488)), (5/288230376151711744), by norm_num⟩
  | 7 => ⟨((-278813565/2305843009213693952), (306833201/9223372036854775808)), (13/9223372036854775808), by norm_num⟩
  | 8 => ⟨((456271459/147573952589676412928), (-869279637/147573952589676412928)), (1/9223372036854775808), by norm_num⟩
  | 9 => ⟨((548850227/4722366482869645213696), (12293409/36893488147419103232)), (39/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-323425551/18889465931478580854784), (-285950629/37778931862957161709568)), (3/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1104495293/1208925819614629174706176), (-470521345/1208925819614629174706176)), (59/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-174277267/9671406556917033397649408), (957497015/19342813113834066795298816)), (9/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((103/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((103/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((103/16), (3525/512)))⁻¹=value ((1687552/23289241), (-1804800/23289241)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((1687552/23289241), (-1804800/23289241))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((65069383/17592186044416), (-18280557/35184372088832)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((-520924033/1125899906842624), (730992251/562949953421312)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((-909489381/4503599627370496), (-972733839/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 3 => ⟨((1667173995/36028797018963968), (-479808805/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 4 => ⟨((-175934951/144115188075855872), (116695715/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-734848775/1152921504606846976), (-555961323/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 6 => ⟨((182248529/2305843009213693952), (-367333355/9223372036854775808)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((20850299/147573952589676412928), (1347295381/147573952589676412928)), (33/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-59648795/73786976294838206464), (-219269179/590295810358705651712)), (1/36893488147419103232), by norm_num⟩
  | 9 => ⟨((597733337/9444732965739290427392), (-251204825/4722366482869645213696)), (29/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((289970877/151115727451828646838272), (538528905/75557863725914323419136)), (51/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-758872399/1208925819614629174706176), (-257141207/2417851639229258349412352)), (85/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((576426179/19342813113834066795298816), (-854524001/19342813113834066795298816)), (35/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((119/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((1949696/26926489), (-1804800/26926489)), 0, by norm_num⟩
  | 1 => ⟨((-272005726208/725035809867121), (3518811340800/725035809867121)), 0, by norm_num⟩
  | 2 => ⟨((-655609333/4398046511104), (-103509041/549755813888)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((823796621/70368744177664), (256250613/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-545899179/1125899906842624), (183757005/562949953421312)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((238306991/36028797018963968), (-1011215051/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((202093149/288230376151711744), (713545207/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((-308372443/4611686018427387904), (-393201389/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((231339477/73786976294838206464), (-433648565/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-303498219/4722366482869645213696), (186847147/1180591620717411303424)), (25/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-224955481/75557863725914323419136), (-297838181/37778931862957161709568)), (57/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((899439359/2417851639229258349412352), (448859511/2417851639229258349412352)), (65/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-1523397999/77371252455336267181195264), (222284773/38685626227668133590597632)), (73/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((119/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((119/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((119/16), (3525/512)))⁻¹=value ((1949696/26926489), (-1804800/26926489)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((1949696/26926489), (-1804800/26926489))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((524659939/2251799813685248), (-160743407/562949953421312)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((492399579/9007199254740992), (644824711/4503599627370496)), (13/9007199254740992), by norm_num⟩
  | 2 => ⟨((-323155019/9007199254740992), (-196542291/36028797018963968)), (15/36028797018963968), by norm_num⟩
  | 3 => ⟨((283883383/72057594037927936), (-730768639/144115188075855872)), (7/72057594037927936), by norm_num⟩
  | 4 => ⟨((53770065/144115188075855872), (998997775/1152921504606846976)), (19/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-1116214573/9223372036854775808), (-102024331/9223372036854775808)), (23/9223372036854775808), by norm_num⟩
  | 6 => ⟨((17998633/2305843009213693952), (-873397425/73786976294838206464)), (13/36893488147419103232), by norm_num⟩
  | 7 => ⟨((217304121/295147905179352825856), (792012819/590295810358705651712)), (7/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1464433031/9444732965739290427392), (31982357/9444732965739290427392)), (57/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((492418627/75557863725914323419136), (-506715527/37778931862957161709568)), (53/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((250920403/302231454903657293676544), (659751143/604462909807314587353088)), (3/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-576498567/4835703278458516698824704), (219366865/9671406556917033397649408)), (83/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((425957199/154742504910672534362390528), (-1549410745/154742504910672534362390528)), (139/154742504910672534362390528), by norm_num⟩
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
  | 0 => ⟨((135/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((49152/690845), (-24064/414507)), 0, by norm_num⟩
  | 1 => ⟨((-3633184768/4295401326225), (394264576/95453362805)), 0, by norm_num⟩
  | 2 => ⟨((-29610578280448/329717392135101125), (-305329527062528/1780473917529546075)), 0, by norm_num⟩
  | 3 => ⟨((1150185591/140737488355328), (491688509/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-441510957/1125899906842624), (63581951/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((192240243/18014398509481984), (-554865833/36028797018963968)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((4857579/72057594037927936), (1977543263/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-1006917379/36893488147419103232), (-1053387371/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 8 => ⟨((265587387/147573952589676412928), (32979891/147573952589676412928)), (13/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-665937615/9444732965739290427392), (418307305/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((369524371/302231454903657293676544), (-1094756215/302231454903657293676544)), (15/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((18632371/302231454903657293676544), (794735123/4835703278458516698824704)), (1/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-16837087/2417851639229258349412352), (-156945793/38685626227668133590597632)), (67/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((135/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((135/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((135/16), (3525/512)))⁻¹=value ((49152/690845), (-24064/414507)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((49152/690845), (-24064/414507))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12885/36028797018963968), (-1219279023/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 1 => ⟨((950008023/72057594037927936), (592105697/72057594037927936)), (15/72057594037927936), by norm_num⟩
  | 2 => ⟨((-257736723/72057594037927936), (514521837/288230376151711744)), (19/288230376151711744), by norm_num⟩
  | 3 => ⟨((141450295/2305843009213693952), (-1745094839/2305843009213693952)), (9/576460752303423488), by norm_num⟩
  | 4 => ⟨((891303417/9223372036854775808), (316785585/4611686018427387904)), (13/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-1083495385/73786976294838206464), (487008291/73786976294838206464)), (33/73786976294838206464), by norm_num⟩
  | 6 => ⟨((117446727/590295810358705651712), (-577410711/295147905179352825856)), (39/590295810358705651712), by norm_num⟩
  | 7 => ⟨((424978145/2361183241434822606848), (302437831/2361183241434822606848)), (43/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-791689625/37778931862957161709568), (374402879/37778931862957161709568)), (45/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((43165085/302231454903657293676544), (-1386315195/604462909807314587353088)), (85/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((444704609/2417851639229258349412352), (557024701/4835703278458516698824704)), (79/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-164914977/9671406556917033397649408), (378189335/38685626227668133590597632)), (35/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-38756431/618970019642690137449562112), (-1061490811/618970019642690137449562112)), (15/77371252455336267181195264), by norm_num⟩
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
  | 0 => ⟨((151/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((2473984/35773849), (-1804800/35773849)), 0, by norm_num⟩
  | 1 => ⟨((-1431646896128/1279768272274801), (4465046323200/1279768272274801)), 0, by norm_num⟩
  | 2 => ⟨((-433889039/8796093022208), (-654693295/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((384260073/70368744177664), (274649623/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-646881877/2251799813685248), (12553355/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((177676969/18014398509481984), (-529110887/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-89824339/576460752303423488), (1159147261/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 7 => ⟨((-538106175/73786976294838206464), (-786311061/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 8 => ⟨((932420657/1180591620717411303424), (326435989/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-1558723919/37778931862957161709568), (945355/1180591620717411303424)), (47/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((425077031/302231454903657293676544), (-322920389/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-419369629/19342813113834066795298816), (1400870363/19342813113834066795298816)), (89/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-333378067/309485009821345068724781056), (-472144797/154742504910672534362390528)), (43/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((151/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((151/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((151/16), (3525/512)))⁻¹=value ((2473984/35773849), (-1804800/35773849)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((2473984/35773849), (-1804800/35773849))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-246048213/144115188075855872), (-168642745/72057594037927936)), (17/288230376151711744), by norm_num⟩
  | 1 => ⟨((1665261151/1152921504606846976), (-68037045/1152921504606846976)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((-474439667/2305843009213693952), (197367355/576460752303423488)), (11/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-327070261/9223372036854775808), (-1336692155/18446744073709551616)), (21/9223372036854775808), by norm_num⟩
  | 4 => ⟨((121771589/9223372036854775808), (54834589/36893488147419103232)), (1/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-86812213/73786976294838206464), (218247511/147573952589676412928)), (43/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-385165933/4722366482869645213696), (-266986871/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((518213273/18889465931478580854784), (209297099/37778931862957161709568)), (29/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-153957501/75557863725914323419136), (677921047/302231454903657293676544)), (31/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-13895629/151115727451828646838272), (-1425431435/4835703278458516698824704)), (61/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((1127539327/38685626227668133590597632), (126891621/19342813113834066795298816)), (29/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-575437789/309485009821345068724781056), (632809115/309485009821345068724781056)), (105/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-386904169/4951760157141521099596496896), (-288494169/1237940039285380274899124224)), (23/618970019642690137449562112), by norm_num⟩
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
  | 0 => ⟨((167/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((2736128/40983961), (-1804800/40983961)), 0, by norm_num⟩
  | 1 => ⟨((-2114546696192/1679685059249521), (4938163814400/1679685059249521)), 0, by norm_num⟩
  | 2 => ⟨((-99879897/4398046511104), (-1107034125/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((248345303/70368744177664), (1041758005/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-448778779/2251799813685248), (-206427843/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((1104195209/144115188075855872), (-12872095/4503599627370496)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((-444624589/2305843009213693952), (19031115/72057594037927936)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((45845987/73786976294838206464), (-1927582229/147573952589676412928)), (29/147573952589676412928), by norm_num⟩
  | 8 => ⟨((630103943/2361183241434822606848), (530900113/1180591620717411303424)), (27/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-1421192877/75557863725914323419136), (-345112515/37778931862957161709568)), (49/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((501101761/604462909807314587353088), (-132036993/1208925819614629174706176)), (45/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-977497223/38685626227668133590597632), (423589517/19342813113834066795298816)), (81/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((27951637/77371252455336267181195264), (-1593668221/1237940039285380274899124224)), (9/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((167/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((167/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((167/16), (3525/512)))⁻¹=value ((2736128/40983961), (-1804800/40983961)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((2736128/40983961), (-1804800/40983961))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-500469833/2305843009213693952), (-373834795/4611686018427387904)), (31/4611686018427387904), by norm_num⟩
  | 1 => ⟨((948712383/9223372036854775808), (-321059831/4611686018427387904)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-322723/576460752303423488), (168358681/4611686018427387904)), (11/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-936142509/147573952589676412928), (-332558293/73786976294838206464)), (45/147573952589676412928), by norm_num⟩
  | 4 => ⟨((742503967/590295810358705651712), (-556527749/1180591620717411303424)), (71/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-53159811/1180591620717411303424), (458009447/2361183241434822606848)), (25/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-343256843/18889465931478580854784), (-358379383/18889465931478580854784)), (31/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((936860713/302231454903657293676544), (-182865109/302231454903657293676544)), (71/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-308051387/2417851639229258349412352), (396440259/1208925819614629174706176)), (39/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-854458829/38685626227668133590597632), (-1136646405/38685626227668133590597632)), (155/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((560002875/154742504910672534362390528), (-54329367/154742504910672534362390528)), (151/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-364350037/2475880078570760549798248448), (767000955/2475880078570760549798248448)), (35/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-43049663/2475880078570760549798248448), (-1018024585/39614081257132168796771975168)), (249/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((183/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((999424/15572787), (-601600/15572787)), 0, by norm_num⟩
  | 1 => ⟨((-106154295296/80837231649123), (601253478400/242511694947369)), 0, by norm_num⟩
  | 2 => ⟨((-6322765/1099511627776), (-1845810027/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((311195493/140737488355328), (458206083/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1205534807/9007199254740992), (-556307765/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((790874579/144115188075855872), (-173905835/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-379178453/2305843009213693952), (578129507/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((6583879/2305843009213693952), (-531195357/73786976294838206464)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((223989405/4722366482869645213696), (1351356229/4722366482869645213696)), (11/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-266320035/37778931862957161709568), (-624589971/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((233249603/604462909807314587353088), (312128013/2417851639229258349412352)), (33/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-575484513/38685626227668133590597632), (256183937/77371252455336267181195264)), (55/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((63969655/154742504910672534362390528), (-974478715/2475880078570760549798248448)), (23/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((183/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((183/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((183/16), (3525/512)))⁻¹=value ((999424/15572787), (-601600/15572787)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((999424/15572787), (-601600/15572787))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-629437563/36893488147419103232), (58703901/18446744073709551616)), (13/18446744073709551616), by norm_num⟩
  | 1 => ⟨((10140639/2305843009213693952), (-327365011/36893488147419103232)), (29/73786976294838206464), by norm_num⟩
  | 2 => ⟨((414583361/295147905179352825856), (807003835/295147905179352825856)), (21/147573952589676412928), by norm_num⟩
  | 3 => ⟨((-400878005/590295810358705651712), (-247438363/2361183241434822606848)), (87/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((815374823/9444732965739290427392), (-836809601/9444732965739290427392)), (9/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((267841665/75557863725914323419136), (706426825/37778931862957161709568)), (13/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-717526215/302231454903657293676544), (-39560411/37778931862957161709568)), (133/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((1315180451/4835703278458516698824704), (-826114501/4835703278458516698824704)), (39/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-4525219/4835703278458516698824704), (354968019/9671406556917033397649408)), (173/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-1000093411/309485009821345068724781056), (-689595699/309485009821345068724781056)), (89/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((113093475/309485009821345068724781056), (-379441629/2475880078570760549798248448)), (11/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-247292601/39614081257132168796771975168), (743610925/19807040628566084398385987584)), (83/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-834595737/316912650057057350374175801344), (-729800047/316912650057057350374175801344)), (301/316912650057057350374175801344), by norm_num⟩
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
  | 0 => ⟨((199/16), (3525/512)), 0, by norm_num⟩
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
  | 0 => ⟨((3260416/52977049), (-1804800/52977049)), 0, by norm_num⟩
  | 1 => ⟨((-3686504726528/2806567720748401), (5884398796800/2806567720748401)), 0, by norm_num⟩
  | 2 => ⟨((41393387/8796093022208), (-1528628975/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((375853363/281474976710656), (775185487/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-198160761/2251799813685248), (-558456781/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1084922299/288230376151711744), (117859115/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-566284491/4611686018427387904), (237657333/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((856158861/295147905179352825856), (-542692975/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-251438539/9444732965739290427392), (1535458943/9444732965739290427392)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-147339431/75557863725914323419136), (-824512695/151115727451828646838272)), (3/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((369798807/2417851639229258349412352), (162819033/1208925819614629174706176)), (19/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-541641201/77371252455336267181195264), (-238172677/154742504910672534362390528)), (59/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((598267423/2475880078570760549798248448), (-177973835/2475880078570760549798248448)), (91/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((199/16), (3525/512)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((199/16), (3525/512)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((199/16), (3525/512)))⁻¹=value ((3260416/52977049), (-1804800/52977049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((3260416/52977049), (-1804800/52977049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-138953055/147573952589676412928), (114676617/147573952589676412928)), (81/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-37529423/2361183241434822606848), (-217189873/295147905179352825856)), (95/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((454813477/2361183241434822606848), (168583155/1180591620717411303424)), (9/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-253709581/4722366482869645213696), (73542751/4722366482869645213696)), (77/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((139128623/37778931862957161709568), (-1479164581/151115727451828646838272)), (133/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((34325953/37778931862957161709568), (842608249/604462909807314587353088)), (99/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-1129085277/4835703278458516698824704), (-6639981/604462909807314587353088)), (65/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((353786647/19342813113834066795298816), (-905962847/38685626227668133590597632)), (39/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((159208685/154742504910672534362390528), (64274367/19342813113834066795298816)), (11/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-898865989/2475880078570760549798248448), (-276731129/2475880078570760549798248448)), (185/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((150257469/4951760157141521099596496896), (-487763485/19807040628566084398385987584)), (93/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((120590991/316912650057057350374175801344), (150448663/39614081257132168796771975168)), (89/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-803514715/2535301200456458802993406410752), (-51464795/316912650057057350374175801344)), (329/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((55496405/4398046511104), (10580093/34359738368)), (621/2199023255552), by norm_num⟩
  | 1 => ⟨((-229515545/1099511627776), (337966717/1099511627776)), (1267/2199023255552), by norm_num⟩
  | 2 => ⟨((-452733977/2199023255552), (327772047/4398046511104)), (339/549755813888), by norm_num⟩
  | 3 => ⟨((-1425426605/17592186044416), (-194082847/8796093022208)), (7989/17592186044416), by norm_num⟩
  | 4 => ⟨((-270027873/17592186044416), (-628936405/35184372088832)), (2255/8796093022208), by norm_num⟩
  | 5 => ⟨((-49575417/70368744177664), (-719075651/140737488355328)), (33093/281474976710656), by norm_num⟩
  | 6 => ⟨((204444231/562949953421312), (-950439555/1125899906842624)), (51241/1125899906842624), by norm_num⟩
  | 7 => ⟨((981524711/9007199254740992), (-757469729/9007199254740992)), (68789/4503599627370496), by norm_num⟩
  | 8 => ⟨((1261413495/72057594037927936), (-30625591/9007199254740992)), (163327/36028797018963968), by norm_num⟩
  | 9 => ⟨((1152150363/576460752303423488), (33706641/72057594037927936)), (696369/576460752303423488), by norm_num⟩
  | 10 => ⟨((810820287/4611686018427387904), (284925839/2305843009213693952)), (168649/576460752303423488), by norm_num⟩
  | 11 => ⟨((436166587/36893488147419103232), (1261222417/73786976294838206464)), (4798849/73786976294838206464), by norm_num⟩
  | 12 => ⟨((9322503/18446744073709551616), (531210507/295147905179352825856)), (7900099/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((55496405/4398046511104), (10580093/34359738368)), (1243/4398046511104), by norm_num⟩
  | 1 => ⟨((-229515545/1099511627776), (337966717/1099511627776)), (317/549755813888), by norm_num⟩
  | 2 => ⟨((-452733977/2199023255552), (327772047/4398046511104)), (2713/4398046511104), by norm_num⟩
  | 3 => ⟨((-1425426605/17592186044416), (-194082847/8796093022208)), (3995/8796093022208), by norm_num⟩
  | 4 => ⟨((-270027873/17592186044416), (-628936405/35184372088832)), (4511/17592186044416), by norm_num⟩
  | 5 => ⟨((-49575417/70368744177664), (-719075651/140737488355328)), (33105/281474976710656), by norm_num⟩
  | 6 => ⟨((204444231/562949953421312), (-950439555/1125899906842624)), (51287/1125899906842624), by norm_num⟩
  | 7 => ⟨((981524711/9007199254740992), (-757469729/9007199254740992)), (137939/9007199254740992), by norm_num⟩
  | 8 => ⟨((1261413495/72057594037927936), (-30625591/9007199254740992)), (329537/72057594037927936), by norm_num⟩
  | 9 => ⟨((1152150363/576460752303423488), (33706641/72057594037927936)), (179857/144115188075855872), by norm_num⟩
  | 10 => ⟨((810820287/4611686018427387904), (284925839/2305843009213693952)), (383415/1152921504606846976), by norm_num⟩
  | 11 => ⟨((436166587/36893488147419103232), (1261222417/73786976294838206464)), (7750329/73786976294838206464), by norm_num⟩
  | 12 => ⟨((9322503/18446744073709551616), (531210507/295147905179352825856)), (7877983/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile042Gamma
