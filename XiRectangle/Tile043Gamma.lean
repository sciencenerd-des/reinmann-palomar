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
namespace Reinmann.XiRectangle.Tile043Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (17907/1280)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (17907/1280))
  have he : value ((7/8), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((23/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((215/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((88064000/1504020649), (-45841920/1504020649)), 0, by norm_num⟩
  | 1 => ⟨((-2826893233356800/2262078112618381201), (4037022842880000/2262078112618381201)), 0, by norm_num⟩
  | 2 => ⟨((165162453/17592186044416), (-78387283/1099511627776)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((228453835/281474976710656), (1255524539/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1040334361/18014398509481984), (-476700839/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((1439573519/576460752303423488), (192919909/288230376151711744)), (7/576460752303423488), by norm_num⟩
  | 6 => ⟨((-768405623/9223372036854775808), (170286047/9223372036854775808)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((636827783/295147905179352825856), (-534261383/295147905179352825856)), (9/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-336059581/9444732965739290427392), (811080383/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-80708797/302231454903657293676544), (-461869187/151115727451828646838272)), (41/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((263046815/4835703278458516698824704), (826033871/9671406556917033397649408)), (15/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-447849639/154742504910672534362390528), (-517298267/309485009821345068724781056)), (11/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((34106183/309485009821345068724781056), (47816151/9903520314283042199192993792)), (1/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((215/16), (17907/2560)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((215/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((215/16), (17907/2560)))⁻¹=value ((88064000/1504020649), (-45841920/1504020649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((88064000/1504020649), (-45841920/1504020649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((182397957/67108864), (32209165/67108864)), (1/268435456), by norm_num⟩
  | 1 => ⟨((44032000/1504020649), (-22920960/1504020649)), 0, by norm_num⟩
  | 2 => ⟨((-706723308339200/2262078112618381201), (1009255710720000/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((55054151/35184372088832), (-1672262037/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((228453835/2251799813685248), (1255524539/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-832267489/144115188075855872), (-381360671/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((959715679/4611686018427387904), (257226545/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-878177855/147573952589676412928), (194612625/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 8 => ⟨((636827783/4722366482869645213696), (-534261383/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-597439255/302231454903657293676544), (1441920681/302231454903657293676544)), (13/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-129134075/9671406556917033397649408), (-738990699/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((382613549/154742504910672534362390528), (300375953/77371252455336267181195264)), (45/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-149283213/1237940039285380274899124224), (-689731023/9903520314283042199192993792)), (59/9903520314283042199192993792), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-6959/276736), (381/40960)), 0, by norm_num⟩
  | 45 => ⟨((362084153177/16322553446400), (-1505331/120586240)), 0, by norm_num⟩
  | 44 => ⟨((-38283647570441/1838572420202496), (55464659959079/4741643894784000)), 0, by norm_num⟩
  | 43 => ⟨((737936811/34359738368), (-377154209/34359738368)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-771388937/34359738368), (191508375/17179869184)), (1/34359738368), by norm_num⟩
  | 41 => ⟨((794136893/34359738368), (-398580361/34359738368)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-811927041/34359738368), (411017981/34359738368)), (1/17179869184), by norm_num⟩
  | 39 => ⟨((415682103/17179869184), (-420787487/34359738368)), (1/17179869184), by norm_num⟩
  | 38 => ⟨((-106673855/4294967296), (430849725/34359738368)), (1/17179869184), by norm_num⟩
  | 37 => ⟨((219239361/8589934592), (-442090917/34359738368)), (1/17179869184), by norm_num⟩
  | 36 => ⟨((-7043851/268435456), (227097087/17179869184)), (1/17179869184), by norm_num⟩
  | 35 => ⟨((463769979/17179869184), (-466911535/34359738368)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-955006255/34359738368), (480283147/34359738368)), (1/17179869184), by norm_num⟩
  | 33 => ⟨((492091485/17179869184), (-247216241/17179869184)), (1/17179869184), by norm_num⟩
  | 32 => ⟨((-1015207591/34359738368), (509454139/34359738368)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((262061501/8589934592), (-32838961/2147483648)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-1083501795/34359738368), (542424769/34359738368)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((1121209469/34359738368), (-560560867/34359738368)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-580817375/17179869184), (72493827/4294967296)), (1/17179869184), by norm_num⟩
  | 27 => ⟨((150635205/4294967296), (-150182309/8589934592)), (1/17179869184), by norm_num⟩
  | 26 => ⟨((-19560959/536870912), (623051287/34359738368)), (1/17179869184), by norm_num⟩
  | 25 => ⟨((325625543/8589934592), (-323547539/17179869184)), (1/17179869184), by norm_num⟩
  | 24 => ⟨((-1357360909/34359738368), (336533815/17179869184)), (1/17179869184), by norm_num⟩
  | 23 => ⟨((1417038033/34359738368), (-350605291/17179869184)), (1/17179869184), by norm_num⟩
  | 22 => ⟨((-741098355/17179869184), (365903827/17179869184)), (1/8589934592), by norm_num⟩
  | 21 => ⟨((776813749/17179869184), (-382597103/17179869184)), (1/8589934592), by norm_num⟩
  | 20 => ⟨((-816140233/17179869184), (400884785/17179869184)), (1/8589934592), by norm_num⟩
  | 19 => ⟨((859653741/17179869184), (-421006527/17179869184)), (1/8589934592), by norm_num⟩
  | 18 => ⟨((-908059361/17179869184), (443252499/17179869184)), (1/8589934592), by norm_num⟩
  | 17 => ⟨((962229635/17179869184), (-233988713/8589934592)), (1/8589934592), by norm_num⟩
  | 16 => ⟨((-511628659/8589934592), (123904895/4294967296)), (1/8589934592), by norm_num⟩
  | 15 => ⟨((546264701/8589934592), (-263363443/8589934592)), (1/8589934592), by norm_num⟩
  | 14 => ⟨((-1171833087/17179869184), (280996733/8589934592)), (1/8589934592), by norm_num⟩
  | 13 => ⟨((1263511017/17179869184), (-301155911/8589934592)), (1/8589934592), by norm_num⟩
  | 12 => ⟨((-1370694693/17179869184), (20276533/536870912)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((748833041/8589934592), (-175790281/4294967296)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-825218841/8589934592), (383684613/8589934592)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((918860889/8589934592), (-422220821/8589934592)), (3/8589934592), by norm_num⟩
  | 8 => ⟨((-1036315535/8589934592), (29333207/536870912)), (3/8589934592), by norm_num⟩
  | 7 => ⟨((2320161/16777216), (-528225481/8589934592)), (3/8589934592), by norm_num⟩
  | 6 => ⟨((-1390977969/8589934592), (301968825/4294967296)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((419182423/2147483648), (-352417889/4294967296)), (1/2147483648), by norm_num⟩
  | 4 => ⟨((-1053940219/4294967296), (422960465/4294967296)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((1415539915/4294967296), (-528504105/4294967296)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-535784601/1073741824), (87936585/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((67666399/67108864), (-262402901/1073741824)), (1/536870912), by norm_num⟩
  | 0 => ⟨((-117354321/2147483648), (515346639/1073741824)), (3/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-41/256), (17907/40960)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-41/256), (17907/40960)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-41/256), (17907/40960))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((182397957/67108864), (32209165/67108864)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((215/16), (17907/2560))) (z:=((-41/256), (17907/40960))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((182397957/67108864), (32209165/67108864))) (r:=(1/268435456)) (by norm_num) ?_ hs
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
  | 0 => ⟨((207/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((133404561/4194304), (423141383/16777216)), (3/33554432), by norm_num⟩
  | 1 => ⟨((247542129/134217728), (16615945/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((16909620958361600/2262078112618381201), (-9123027139085760/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((-464897485/8796093022208), (176585041/2199023255552)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((81551573/562949953421312), (-1829202603/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((234779785/18014398509481984), (1099759799/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-674809453/1152921504606846976), (-135158553/288230376151711744)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1316362379/73786976294838206464), (122660017/36893488147419103232)), (119/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1037384801/2361183241434822606848), (164088987/1180591620717411303424)), (147/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((640749045/75557863725914323419136), (-327569545/37778931862957161709568)), (101/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-222833941/2417851639229258349412352), (1523031897/4835703278458516698824704)), (137/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-285222459/154742504910672534362390528), (-1375271517/154742504910672534362390528)), (361/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((404358911/2475880078570760549798248448), (243358823/1237940039285380274899124224)), (949/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215/16), (-17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((77043601/4194304), (76446517/4194304)), (1/8388608), by norm_num⟩
  | 1 => ⟨((180433265/134217728), (16615945/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((16909620958361600/2262078112618381201), (-9123027139085760/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((-464897485/8796093022208), (176585041/2199023255552)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((81551573/562949953421312), (-1829202603/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((234779785/18014398509481984), (1099759799/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-674809453/1152921504606846976), (-135158553/288230376151711744)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1316362379/73786976294838206464), (122660017/36893488147419103232)), (119/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1037384801/2361183241434822606848), (164088987/1180591620717411303424)), (147/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((640749045/75557863725914323419136), (-327569545/37778931862957161709568)), (101/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-222833941/2417851639229258349412352), (1523031897/4835703278458516698824704)), (137/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-285222459/154742504910672534362390528), (-1375271517/154742504910672534362390528)), (361/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((404358911/2475880078570760549798248448), (243358823/1237940039285380274899124224)), (949/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((647183269/33554432), (76446517/4194304)), (5/33554432), by norm_num⟩
  | 1 => ⟨((180433265/134217728), (16615945/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((16909620958361600/2262078112618381201), (-9123027139085760/2262078112618381201)), 0, by norm_num⟩
  | 3 => ⟨((-464897485/8796093022208), (176585041/2199023255552)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((81551573/562949953421312), (-1829202603/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 5 => ⟨((234779785/18014398509481984), (1099759799/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-674809453/1152921504606846976), (-135158553/288230376151711744)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1316362379/73786976294838206464), (122660017/36893488147419103232)), (119/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1037384801/2361183241434822606848), (164088987/1180591620717411303424)), (147/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((640749045/75557863725914323419136), (-327569545/37778931862957161709568)), (101/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-222833941/2417851639229258349412352), (1523031897/4835703278458516698824704)), (137/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-285222459/154742504910672534362390528), (-1375271517/154742504910672534362390528)), (361/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((404358911/2475880078570760549798248448), (243358823/1237940039285380274899124224)), (949/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5653786466713600/2262078112618381201), (-8074045685760000/2262078112618381201)), 0, by norm_num⟩
  | 1 => ⟨((-165162453/4398046511104), (78387283/274877906944)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-342680753/70368744177664), (-235410851/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1040334361/2251799813685248), (476700839/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-899733449/36028797018963968), (-120574943/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((576304217/576460752303423488), (-127714535/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-1114448619/36893488147419103232), (934957421/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 7 => ⟨((84014895/147573952589676412928), (-811080383/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((90797397/18889465931478580854784), (519602835/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-657617037/604462909807314587353088), (-516271169/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((615793253/9671406556917033397649408), (711285117/19342813113834066795298816)), (17/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-1637096783/618970019642690137449562112), (-17931057/154742504910672534362390528)), (51/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((424848883/4951760157141521099596496896), (-396052801/9903520314283042199192993792)), (19/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((165162453/4398046511104), (-78387283/274877906944)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((342680753/35184372088832), (235410851/8796093022208)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-780250771/562949953421312), (-357525629/281474976710656)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((899733449/9007199254740992), (120574943/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((-720380271/144115188075855872), (159643169/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((52239779/288230376151711744), (-701218065/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-588104265/147573952589676412928), (1419390669/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-90797397/2361183241434822606848), (-519602835/1180591620717411303424)), (11/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((739819167/75557863725914323419136), (580805065/37778931862957161709568)), (9/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-384870783/604462909807314587353088), (-222276599/604462909807314587353088)), (15/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((562752019/19342813113834066795298816), (24655203/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-159318331/154742504910672534362390528), (594079201/1237940039285380274899124224)), (37/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((263762165/9903520314283042199192993792), (-171808943/4951760157141521099596496896)), (29/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-228453835/35184372088832), (-1255524539/70368744177664)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((1040334361/562949953421312), (953401677/562949953421312)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((-899733449/4503599627370496), (-120574943/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((240126757/18014398509481984), (-212857559/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 4 => ⟨((-696530387/1152921504606846976), (146087097/288230376151711744)), (5/1152921504606846976), by norm_num⟩
  | 5 => ⟨((588104265/36893488147419103232), (-1419390669/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 6 => ⟨((105930297/590295810358705651712), (606203307/295147905179352825856)), (11/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-246606389/4722366482869645213696), (-774406753/9444732965739290427392)), (11/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1154612349/302231454903657293676544), (666829797/302231454903657293676544)), (19/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-1875840063/9671406556917033397649408), (-82184011/9671406556917033397649408)), (1/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((584167213/77371252455336267181195264), (-544572601/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-527524329/2475880078570760549798248448), (171808943/618970019642690137449562112)), (23/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((99411503/39614081257132168796771975168), (-563180161/39614081257132168796771975168)), (9/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1040334361/1125899906842624), (-476700839/562949953421312)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((899733449/4503599627370496), (120574943/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((-720380271/36028797018963968), (159643169/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((696530387/576460752303423488), (-146087097/144115188075855872)), (7/576460752303423488), by norm_num⟩
  | 4 => ⟨((-183782583/4611686018427387904), (13861237/144115188075855872)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-79447723/147573952589676412928), (-1818609921/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((431561181/2361183241434822606848), (677605909/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-1154612349/75557863725914323419136), (-166707449/18889465931478580854784)), (9/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((1055160035/1208925819614629174706176), (23114253/604462909807314587353088)), (17/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-1460418033/38685626227668133590597632), (680715751/38685626227668133590597632)), (15/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((725345953/618970019642690137449562112), (-472474593/309485009821345068724781056)), (27/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-74558627/4951760157141521099596496896), (844770241/9903520314283042199192993792)), (23/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-363030873/316912650057057350374175801344), (-576089025/158456325028528675187087900672)), (39/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1439573519/18014398509481984), (-192919909/9007199254740992)), (7/18014398509481984), by norm_num⟩
  | 1 => ⟨((576304217/36028797018963968), (-255429071/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((-52239779/36028797018963968), (701218065/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 3 => ⟨((588104265/9223372036854775808), (-1419390669/9223372036854775808)), (15/9223372036854775808), by norm_num⟩
  | 4 => ⟨((158895445/147573952589676412928), (1818609921/147573952589676412928)), (5/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-517873417/1180591620717411303424), (-406563545/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 6 => ⟨((202057161/4722366482869645213696), (466780857/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-211032007/75557863725914323419136), (-73965609/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((1314376229/9671406556917033397649408), (-38290261/604462909807314587353088)), (27/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-22667061/4835703278458516698824704), (472474593/77371252455336267181195264)), (13/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((164028979/2475880078570760549798248448), (-929247265/2475880078570760549798248448)), (3/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((54454631/9903520314283042199192993792), (345653415/19807040628566084398385987584)), (21/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-766689517/1267650600228229401496703205376), (-767009355/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-768405623/144115188075855872), (170286047/144115188075855872)), (11/288230376151711744), by norm_num⟩
  | 1 => ⟨((1114448619/1152921504606846976), (-934957421/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-588104265/9223372036854775808), (1419390669/9223372036854775808)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((-105930297/73786976294838206464), (-606203307/36893488147419103232)), (15/73786976294838206464), by norm_num⟩
  | 4 => ⟨((107890295/147573952589676412928), (677605909/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-202057161/2361183241434822606848), (-466780857/9444732965739290427392)), (15/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1969632065/302231454903657293676544), (43146605/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-876250819/2417851639229258349412352), (408429451/2417851639229258349412352)), (5/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((68001183/4835703278458516698824704), (-708711889/38685626227668133590597632)), (21/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-1067897/4835703278458516698824704), (1548745441/1237940039285380274899124224)), (41/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-399333961/19807040628566084398385987584), (-633697927/9903520314283042199192993792)), (39/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((766689517/316912650057057350374175801344), (383504677/158456325028528675187087900672)), (37/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-819235511/5070602400912917605986812821504), (-8078195/158456325028528675187087900672)), (17/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-636827783/2305843009213693952), (534261383/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 1 => ⟨((84014895/2305843009213693952), (-811080383/9223372036854775808)), (11/9223372036854775808), by norm_num⟩
  | 2 => ⟨((90797397/73786976294838206464), (1039205669/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-246606389/295147905179352825856), (-774406753/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 4 => ⟨((1154612349/9444732965739290427392), (666829797/9444732965739290427392)), (13/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-211032007/18889465931478580854784), (-73965609/151115727451828646838272)), (35/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((876250819/1208925819614629174706176), (-408429451/1208925819614629174706176)), (23/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-310862551/9671406556917033397649408), (809956445/19342813113834066795298816)), (27/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((175745335/309485009821345068724781056), (-995622069/309485009821345068724781056)), (15/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((285238543/4951760157141521099596496896), (905282753/4951760157141521099596496896)), (31/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-301199453/39614081257132168796771975168), (-602650207/79228162514264337593543950336)), (31/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((1404403733/2535301200456458802993406410752), (443146697/2535301200456458802993406410752)), (59/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-1212682823/40564819207303340847894502572032), (213538985/40564819207303340847894502572032)), (7/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-336059581/36893488147419103232), (811080383/36893488147419103232)), (7/18446744073709551616), by norm_num⟩
  | 1 => ⟨((-45398699/73786976294838206464), (-519602835/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 2 => ⟨((369909583/590295810358705651712), (1161610129/1180591620717411303424)), (27/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-1154612349/9444732965739290427392), (-166707449/2361183241434822606848)), (29/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((1055160035/75557863725914323419136), (23114253/37778931862957161709568)), (27/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-1314376229/1208925819614629174706176), (38290261/75557863725914323419136)), (5/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((68001183/1208925819614629174706176), (-708711889/9671406556917033397649408)), (27/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-175745335/154742504910672534362390528), (497811035/77371252455336267181195264)), (35/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((-320893361/2475880078570760549798248448), (-1018443097/2475880078570760549798248448)), (5/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((752998633/39614081257132168796771975168), (753312759/39614081257132168796771975168)), (11/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-482763783/316912650057057350374175801344), (-304663355/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((1819024235/20282409603651670423947251286016), (-320308477/20282409603651670423947251286016)), (45/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-322484479/81129638414606681695789005144064), (61831603/20282409603651670423947251286016)), (11/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80708797/590295810358705651712), (461869187/295147905179352825856)), (41/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-328808519/1180591620717411303424), (-516271169/1180591620717411303424)), (29/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((384870783/4722366482869645213696), (444553197/9444732965739290427392)), (3/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-937920031/75557863725914323419136), (-41092005/75557863725914323419136)), (55/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((91276127/75557863725914323419136), (-680715751/1208925819614629174706176)), (27/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-22667061/302231454903657293676544), (472474593/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((1067897/604462909807314587353088), (-1548745441/154742504910672534362390528)), (61/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((285238543/1237940039285380274899124224), (905282753/1237940039285380274899124224)), (21/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-752998633/19807040628566084398385987584), (-753312759/19807040628566084398385987584)), (51/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((1072808407/316912650057057350374175801344), (338514839/316912650057057350374175801344)), (59/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-1111625921/5070602400912917605986812821504), (195744069/5070602400912917605986812821504)), (1/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((859958611/81129638414606681695789005144064), (-329768549/40564819207303340847894502572032)), (33/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((-105875753/324518553658426726783156020576256), (453800553/649037107316853453566312041152512)), (33/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((263046815/4722366482869645213696), (826033871/9444732965739290427392)), (15/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-1231586507/37778931862957161709568), (-177821279/9444732965739290427392)), (23/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((1125504037/151115727451828646838272), (49310405/151115727451828646838272)), (21/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-584167213/604462909807314587353088), (544572601/1208925819614629174706176)), (51/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((22667061/302231454903657293676544), (-944949185/9671406556917033397649408)), (53/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-164028979/77371252455336267181195264), (929247265/77371252455336267181195264)), (23/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-399333961/1237940039285380274899124224), (-633697927/618970019642690137449562112)), (17/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((301199453/4951760157141521099596496896), (602650207/9903520314283042199192993792)), (3/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-965527567/158456325028528675187087900672), (-304663355/158456325028528675187087900672)), (31/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((555812961/1267650600228229401496703205376), (-195744069/2535301200456458802993406410752)), (75/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-118244309/5070602400912917605986812821504), (90686351/5070602400912917605986812821504)), (85/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((508203615/649037107316853453566312041152512), (-1089121327/649037107316853453566312041152512)), (23/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((50444933/10384593717069655257060992658440192), (1162487151/10384593717069655257060992658440192)), (3/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22016000/4512061947), (-3820160/1504020649)), 0, by norm_num⟩
  | 1 => ⟨((-706723308339200/6786234337855143603), (336418570240000/2262078112618381201)), 0, by norm_num⟩
  | 2 => ⟨((55054151/70368744177664), (-1672262037/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((304605113/4503599627370496), (837016359/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-693556241/144115188075855872), (-635601119/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((959715679/4611686018427387904), (257226545/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-1024540831/147573952589676412928), (227048063/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((849103711/4722366482869645213696), (-712348511/4722366482869645213696)), (13/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-448079441/151115727451828646838272), (1081440511/151115727451828646838272)), (5/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-107611729/4835703278458516698824704), (-1231651165/4835703278458516698824704)), (7/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((701458173/154742504910672534362390528), (1101378495/154742504910672534362390528)), (41/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-149283213/618970019642690137449562112), (-689731023/4951760157141521099596496896)), (59/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((1455197141/158456325028528675187087900672), (15938717/39614081257132168796771975168)), (43/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346993/33554432), (611486909/33554432)), (3/16777216), by norm_num⟩
  | 1 => ⟨((360838575/268435456), (33251851/134217728)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((513749687/68719476736), (-277555925/68719476736)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-464302553/8796093022208), (353987481/4398046511104)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((78842369/562949953421312), (-1834168237/1125899906842624)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((477057349/36028797018963968), (1101769381/36028797018963968)), (15/18014398509481984), by norm_num⟩
  | 6 => ⟨((-341406839/576460752303423488), (-538860399/1152921504606846976)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((166203703/9223372036854775808), (234189589/73786976294838206464)), (121/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-522193021/1180591620717411303424), (172537741/1180591620717411303424)), (37/590295810358705651712), by norm_num⟩
  | 9 => ⟨((159766903/18889465931478580854784), (-674383639/75557863725914323419136)), (51/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-211873657/2417851639229258349412352), (1557449975/4835703278458516698824704)), (275/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-161271631/77371252455336267181195264), (-1396825611/154742504910672534362390528)), (725/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((854192733/4951760157141521099596496896), (60964227/309485009821345068724781056)), (953/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-234897711/2251799813685248), (1783746173/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-243684091/9007199254740992), (-1339226175/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109689985/288230376151711744), (1016961789/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 3 => ⟨((-1279620905/4611686018427387904), (-342968727/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 4 => ⟨((512270415/36893488147419103232), (-227048063/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-594372597/1180591620717411303424), (498643957/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 6 => ⟨((418207477/37778931862957161709568), (-252336119/9444732965739290427392)), (5/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((32283519/302231454903657293676544), (1477981397/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-263046815/9671406556917033397649408), (-413016935/9671406556917033397649408)), (7/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((1094743561/618970019642690137449562112), (632253437/618970019642690137449562112)), (11/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-800358427/9903520314283042199192993792), (-70130355/19807040628566084398385987584)), (35/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((906344283/316912650057057350374175801344), (-422456321/316912650057057350374175801344)), (27/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-750256825/10141204801825835211973625643008), (977401987/10141204801825835211973625643008)), (21/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346989/33554432), (76435867/4194304)), (7/33554432), by norm_num⟩
  | 1 => ⟨((1443354271/1073741824), (33251841/134217728)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1027499903/137438953472), (-555111365/137438953472)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-232152497/4398046511104), (176993577/2199023255552)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((157700371/1125899906842624), (-1834171701/1125899906842624)), (21/1125899906842624), by norm_num⟩
  | 5 => ⟨((238519605/18014398509481984), (550892299/18014398509481984)), (31/36028797018963968), by norm_num⟩
  | 6 => ⟨((-682800915/1152921504606846976), (-269445601/576460752303423488)), (49/1152921504606846976), by norm_num⟩
  | 7 => ⟨((664818753/36893488147419103232), (117139899/36893488147419103232)), (61/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-522225131/1180591620717411303424), (43121831/295147905179352825856)), (149/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((19975039/2361183241434822606848), (-168576615/18889465931478580854784)), (205/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-212069057/2417851639229258349412352), (1557432853/4835703278458516698824704)), (551/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-322100711/154742504910672534362390528), (-1397031889/154742504910672534362390528)), (363/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((853826397/4951760157141521099596496896), (975904879/4951760157141521099596496896)), (477/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-211369521/288230376151711744), (-387414015/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((365605973/2305843009213693952), (391964259/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-585451903/36893488147419103232), (64870875/18446744073709551616)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((141517285/147573952589676412928), (-949798015/1180591620717411303424)), (3/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-298719627/9444732965739290427392), (1441920679/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-129134077/302231454903657293676544), (-369495349/75557863725914323419136)), (7/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((350729087/2417851639229258349412352), (1101378493/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-938351623/77371252455336267181195264), (-541931517/77371252455336267181195264)), (1/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((1715053771/2475880078570760549798248448), (75139667/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-1186879417/39614081257132168796771975168), (276608305/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((589487505/633825300114114700748351602688), (-47997419/39614081257132168796771975168)), (23/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-242374711/20282409603651670423947251286016), (343271717/5070602400912917605986812821504)), (19/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-147517307/162259276829213363391578010288128), (-117046659/40564819207303340847894502572032)), (33/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346989/33554432), (76435867/4194304)), (1/4194304), by norm_num⟩
  | 1 => ⟨((1443354271/1073741824), (33251841/134217728)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((1027499901/137438953472), (-555111365/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-232152493/4398046511104), (707974301/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((157700335/1125899906842624), (-1834171615/1125899906842624)), (11/562949953421312), by norm_num⟩
  | 5 => ⟨((477039195/36028797018963968), (550892211/18014398509481984)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-170700187/288230376151711744), (-538890939/1152921504606846976)), (25/576460752303423488), by norm_num⟩
  | 7 => ⟨((1329636611/73786976294838206464), (234279281/73786976294838206464)), (123/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-522224313/1180591620717411303424), (2695115/18446744073709551616)), (75/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((79899873/9444732965739290427392), (-674305405/75557863725914323419136)), (103/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-424133617/4835703278458516698824704), (778713497/2417851639229258349412352)), (69/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-10065705/4835703278458516698824704), (-1397021413/154742504910672534362390528)), (727/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((853821895/4951760157141521099596496896), (975890591/4951760157141521099596496896)), (955/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((936723045/295147905179352825856), (-12974175/18446744073709551616)), (1/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-84910371/147573952589676412928), (569878809/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((5600993/147573952589676412928), (-108144051/1180591620717411303424)), (5/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((32283519/37778931862957161709568), (369495349/37778931862957161709568)), (19/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-526093629/1208925819614629174706176), (-413016935/604462909807314587353088)), (15/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((246317301/4835703278458516698824704), (142257023/4835703278458516698824704)), (19/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-150067205/38685626227668133590597632), (-26298883/154742504910672534362390528)), (23/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((1068191475/4951760157141521099596496896), (-248947475/2475880078570760549798248448)), (25/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-331586721/39614081257132168796771975168), (863953541/79228162514264337593543950336)), (13/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((83316307/633825300114114700748351602688), (-943997221/1267650600228229401496703205376)), (13/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((243403557/20282409603651670423947251286016), (772507949/20282409603651670423947251286016)), (49/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((-467315515/324518553658426726783156020576256), (-935020927/649037107316853453566312041152512)), (23/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((998687099/10384593717069655257060992658440192), (78781635/2596148429267413814265248164610048)), (21/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346989/33554432), (76435867/4194304)), (9/33554432), by norm_num⟩
  | 1 => ⟨((1443354271/1073741824), (33251841/134217728)), (1/134217728), by norm_num⟩
  | 2 => ⟨((1027499901/137438953472), (-555111365/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-232152493/4398046511104), (707974301/8796093022208)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((157700335/1125899906842624), (-57317863/35184372088832)), (23/1125899906842624), by norm_num⟩
  | 5 => ⟨((477039197/36028797018963968), (1101784423/36028797018963968)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-42675047/72057594037927936), (-538890939/1152921504606846976)), (51/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1329636627/73786976294838206464), (117139637/36893488147419103232)), (31/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-522224323/1180591620717411303424), (172487373/1180591620717411303424)), (151/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((319599497/37778931862957161709568), (-674305461/75557863725914323419136)), (207/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-424133559/4835703278458516698824704), (778713589/2417851639229258349412352)), (553/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-322102783/154742504910672534362390528), (-349255409/38685626227668133590597632)), (91/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((853822371/4951760157141521099596496896), (975890741/4951760157141521099596496896)), (239/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-579335035/75557863725914323419136), (1398226115/75557863725914323419136)), (25/75557863725914323419136), by norm_num⟩
  | 1 => ⟨((-78263077/151115727451828646838272), (-1791492603/302231454903657293676544)), (1/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((637689247/1208925819614629174706176), (1001253175/1208925819614629174706176)), (3/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-995221419/9671406556917033397649408), (-574775851/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((227374553/19342813113834066795298816), (39846793/77371252455336267181195264)), (47/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-70808147/77371252455336267181195264), (528070401/1237940039285380274899124224)), (35/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((234455257/4951760157141521099596496896), (-610876241/9903520314283042199192993792)), (3/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-302968389/316912650057057350374175801344), (1716358585/316912650057057350374175801344)), (61/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((-276594951/2535301200456458802993406410752), (-438924971/1267650600228229401496703205376)), (35/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((649049327/40564819207303340847894502572032), (649320089/40564819207303340847894502572032)), (39/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-832239249/649037107316853453566312041152512), (-262605451/649037107316853453566312041152512)), (41/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((1567913145/20769187434139310514121985316880384), (-34511351/2596148429267413814265248164610048)), (79/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((-555932839/166153499473114484112975882535043072), (852734835/332306998946228968225951765070086144)), (77/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346989/33554432), (76435867/4194304)), (5/16777216), by norm_num⟩
  | 1 => ⟨((1443354271/1073741824), (33251841/134217728)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((1027499901/137438953472), (-555111365/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-232152493/4398046511104), (707974301/8796093022208)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((157700335/1125899906842624), (-57317863/35184372088832)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((477039197/36028797018963968), (1101784423/36028797018963968)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-42675047/72057594037927936), (-538890939/1152921504606846976)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((1329636627/73786976294838206464), (117139637/36893488147419103232)), (125/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-522224323/1180591620717411303424), (344974745/2361183241434822606848)), (19/295147905179352825856), by norm_num⟩
  | 9 => ⟨((639198995/75557863725914323419136), (-168576365/18889465931478580854784)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-424133565/4835703278458516698824704), (194678397/604462909807314587353088)), (277/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-322102771/154742504910672534362390528), (-698510819/77371252455336267181195264)), (729/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((426911177/2475880078570760549798248448), (487945377/2475880078570760549798248448)), (957/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-516504933/4835703278458516698824704), (-810978397/4835703278458516698824704)), (31/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((1209139343/19342813113834066795298816), (349160539/9671406556917033397649408)), (23/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((-1104990355/77371252455336267181195264), (-48411663/77371252455336267181195264)), (21/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((286760027/154742504910672534362390528), (-267323551/309485009821345068724781056)), (51/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((-356062819/2475880078570760549798248448), (927726335/4951760157141521099596496896)), (53/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((161039351/39614081257132168796771975168), (-1824621203/79228162514264337593543950336)), (91/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((392055613/633825300114114700748351602688), (1244296021/633825300114114700748351602688)), (17/158456325028528675187087900672), by norm_num⟩
  | 7 => ⟨((-147854863/1267650600228229401496703205376), (-591666173/5070602400912917605986812821504)), (3/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((947929651/81129638414606681695789005144064), (149555247/40564819207303340847894502572032)), (31/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((-1091365185/1298074214633706907132624082305024), (192176395/1298074214633706907132624082305024)), (75/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((928713299/20769187434139310514121985316880384), (-356133927/10384593717069655257060992658440192)), (85/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((-498940985/332306998946228968225951765070086144), (267317691/83076749736557242056487941267521536)), (91/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((-49525513/5316911983139663491615228241121378304), (-1141299407/5316911983139663491615228241121378304)), (3/166153499473114484112975882535043072), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647346989/33554432), (76435867/4194304)), (11/33554432), by norm_num⟩
  | 1 => ⟨((1443354271/1073741824), (33251841/134217728)), (5/536870912), by norm_num⟩
  | 2 => ⟨((1027499901/137438953472), (-555111365/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-232152493/4398046511104), (707974301/8796093022208)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((157700335/1125899906842624), (-57317863/35184372088832)), (25/1125899906842624), by norm_num⟩
  | 5 => ⟨((477039197/36028797018963968), (1101784423/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 6 => ⟨((-42675047/72057594037927936), (-538890939/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1329636627/73786976294838206464), (117139637/36893488147419103232)), (63/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-522224323/1180591620717411303424), (344974745/2361183241434822606848)), (153/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((639198995/75557863725914323419136), (-168576365/18889465931478580854784)), (209/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-424133565/4835703278458516698824704), (194678397/604462909807314587353088)), (555/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-322102771/154742504910672534362390528), (-698510819/77371252455336267181195264)), (365/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((426911177/2475880078570760549798248448), (975890753/4951760157141521099596496896)), (479/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((406419065841029/2097152), (-293735240415873/2097152)), (17167313/131072), by norm_num⟩
  | 1 => ⟨((1180823607/4), -140265824), (847/4), by norm_num⟩
  | 2 => ⟨(216670308, (-119073083/2)), (689/4), by norm_num⟩
  | 3 => ⟨((824768841/8), (-164077649/16)), 94, by norm_num⟩
  | 4 => ⟨((1150962937/32), (9208441/4)), (1239/32), by norm_num⟩
  | 5 => ⟨((629969103/64), (283622415/128)), (823/64), by norm_num⟩
  | 6 => ⟨((1128529543/512), (27659481/32)), (1837/512), by norm_num⟩
  | 7 => ⟨((850677885/2048), (244188213/1024)), (443/512), by norm_num⟩
  | 8 => ⟨((1100106731/16384), (860946379/16384)), (377/2048), by norm_num⟩
  | 9 => ⟨((617791531/65536), (639482017/65536)), (575/16384), by norm_num⟩
  | 10 => ⟨((606414007/524288), (412760111/262144)), (1591/262144), by norm_num⟩
  | 11 => ⟨((129921407/1048576), (945069279/4194304)), (2017/2097152), by norm_num⟩
  | 12 => ⟨((383812983/33554432), (60847775/2097152)), (2363/16777216), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((402276582247203/2535301200456458802993406410752), (-815207091239/10141204801825835211973625643008)), (427031/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((906144124378871/316912650057057350374175801344), (-249693968923/158456325028528675187087900672)), (523711/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((240936179543215/4951760157141521099596496896), (-1126410484629/39614081257132168796771975168)), (295349/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1929659780627453/2475880078570760549798248448), (-1199221207709/2475880078570760549798248448)), (314461/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1811366498883745/154742504910672534362390528), (-1201919403745/154742504910672534362390528)), (39399/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((396815332666123/2417851639229258349412352), (-1129674430767/9671406556917033397649408)), (296271/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((645913140189023/302231454903657293676544), (-1936230071/1180591620717411303424)), (520037/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1941559309646579/75557863725914323419136), (-404093210813/18889465931478580854784)), (848003/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((668968066993329/2361183241434822606848), (-1217051140651/4722366482869645213696)), (638589/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1677109695428271/590295810358705651712), (-420309536541/147573952589676412928)), (882283/590295810358705651712), by norm_num⟩
  | 8 => ⟨((946613250892881/36893488147419103232), (-1056652897403/36893488147419103232)), (277307/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1901369374661673/9223372036854775808), (-2393749089391/9223372036854775808)), (628355/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1672921593045995/1152921504606846976), (-2414269501203/1152921504606846976)), (9905/9007199254740992), by norm_num⟩
  | 5 => ⟨((1263993562108227/144115188075855872), (-1067903821669/72057594037927936)), (1122015/144115188075855872), by norm_num⟩
  | 4 => ⟨((1596450609950891/36028797018963968), (-1625476308709/18014398509481984)), (1708665/36028797018963968), by norm_num⟩
  | 3 => ⟨((1621502215341893/9007199254740992), (-4147725442097/9007199254740992)), (68171/281474976710656), by norm_num⟩
  | 2 => ⟨((624043985429033/1125899906842624), (-4276549126173/2251799813685248)), (70359/70368744177664), by norm_num⟩
  | 1 => ⟨((656996791281601/562949953421312), (-6746795984191/1125899906842624)), (889459/281474976710656), by norm_num⟩
  | 0 => ⟨((190241247829135/140737488355328), (-7441346653175/562949953421312)), (1968119/281474976710656), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((190241247829135/140737488355328), (-7441346653175/562949953421312)), (7507778168798351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((514266269008851/281474976710656), (-20117611723395/562949953421312)), (5372823/281474976710656), by norm_num⟩
  | 2 => ⟨((1878451995657717/562949953421312), (-574307774801/4398046511104)), (20016741/281474976710656), by norm_num⟩
  | 3 => ⟨((1564605322976733/140737488355328), (-61323225150811/70368744177664)), (8675715/17592186044416), by norm_num⟩
  | 4 => ⟨((1080445806118897/8796093022208), (-170435478162751/8796093022208)), (52005035/4398046511104), by norm_num⟩
  | 5 => ⟨((252756679529253/17179869184), (-81777383795695/17179869184)), (231111585/68719476736), by norm_num⟩
  | 6 => ⟨((406419065841029/2097152), (-293735240415873/2097152)), (17167313/131072), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((647346989/33554432), (76435867/4194304)), (11/33554432), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((9420800/334203049), (-45841920/334203049)), 0, by norm_num⟩
  | 1 => ⟨((1006365078323200/111691677960896401), (431867559936000/111691677960896401)), 0, by norm_num⟩
  | 2 => ⟨((-862414355/2199023255552), (1239056889/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-145648323/4398046511104), (-612892517/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((25122949/8796093022208), (-501090755/281474976710656)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((184286259/2251799813685248), (995193093/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-293796303/18014398509481984), (180023655/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((67469279/1152921504606846976), (-1330178489/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 8 => ⟨((1444446937/18446744073709551616), (374006565/18446744073709551616)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-368075933/147573952589676412928), (750355571/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-740392295/2361183241434822606848), (-286559411/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 11 => ⟨((795874365/37778931862957161709568), (-683219777/37778931862957161709568)), (11/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((285124067/302231454903657293676544), (1027420569/604462909807314587353088)), (15/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((23/16), (17907/2560)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((23/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((23/16), (17907/2560)))⁻¹=value ((9420800/334203049), (-45841920/334203049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((9420800/334203049), (-45841920/334203049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((5324800/119866083), (-15280640/119866083)), 0, by norm_num⟩
  | 1 => ⟨((34190743961600/4789292617920963), (81366351872000/14367877853762889)), 0, by norm_num⟩
  | 2 => ⟨((-4462767/8589934592), (181011429/549755813888)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-332402049/35184372088832), (-1422457175/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((1568819459/562949953421312), (166518091/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-363677617/4503599627370496), (770389397/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((-656434729/72057594037927936), (-644679193/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((445380177/576460752303423488), (-440355093/1152921504606846976)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((132533699/18446744073709551616), (1064934513/18446744073709551616)), (3/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-566585507/147573952589676412928), (-243295749/295147905179352825856)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((325417283/2361183241434822606848), (-267299585/1180591620717411303424)), (13/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((859123495/75557863725914323419136), (1043727175/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-1369760619/1208925819614629174706176), (126312935/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((39/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((39/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((39/16), (17907/2560)))⁻¹=value ((5324800/119866083), (-15280640/119866083)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((5324800/119866083), (-15280640/119866083))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-650330000588800/40059610410287067), (-388054908928000/40059610410287067)), 0, by norm_num⟩
  | 1 => ⟨((1028708471/549755813888), (-493809669/274877906944)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((280053997/2199023255552), (1030022345/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-1665569069/70368744177664), (393344281/70368744177664)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((39049277/562949953421312), (-73043725/35184372088832)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((1464500269/9007199254740992), (14050231/281474976710656)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-518750483/72057594037927936), (824702847/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((-823291073/1152921504606846976), (-222455849/288230376151711744)), (5/576460752303423488), by norm_num⟩
  | 8 => ⟨((1311913237/18446744073709551616), (-345463973/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 9 => ⟨((99254787/73786976294838206464), (1744006889/295147905179352825856)), (25/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-1065809577/2361183241434822606848), (-9629913/590295810358705651712)), (19/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((366312617/37778931862957161709568), (-1205083363/37778931862957161709568)), (7/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1255128443/604462909807314587353088), (387397349/302231454903657293676544)), (41/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((55/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((22528000/398100649), (-45841920/398100649)), 0, by norm_num⟩
  | 1 => ⟨((796985422643200/158484126734221201), (1032726773760000/158484126734221201)), 0, by norm_num⟩
  | 2 => ⟨((-1137921165/2199023255552), (57814197/549755813888)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((302111195/35184372088832), (-576479783/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((462676153/281474976710656), (800264565/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-1156129759/9007199254740992), (7658731/140737488355328)), (5/9007199254740992), by norm_num⟩
  | 6 => ⟨((71850603/144115188075855872), (-643470491/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((144127359/288230376151711744), (648800269/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((-1119665779/36893488147419103232), (768457455/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-201029253/590295810358705651712), (-172417299/73786976294838206464)), (13/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1361671877/9444732965739290427392), (6863267/147573952589676412928)), (37/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-1021083803/151115727451828646838272), (263884271/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-255059827/1208925819614629174706176), (-1418487141/2417851639229258349412352)), (73/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((55/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((55/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((55/16), (17907/2560)))⁻¹=value ((22528000/398100649), (-45841920/398100649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((22528000/398100649), (-45841920/398100649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1118274987/549755813888), (726340775/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((-262765717/2199023255552), (-1037129669/2199023255552)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((569202369/8796093022208), (5555561/1099511627776)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-396542581/140737488355328), (932339501/140737488355328)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-604417877/1125899906842624), (-534953127/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((1035725745/18014398509481984), (-601012617/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((86804773/72057594037927936), (1651823099/288230376151711744)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((-568770995/1152921504606846976), (-62534085/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((309773325/18446744073709551616), (-1371633731/36893488147419103232)), (19/36893488147419103232), by norm_num⟩
  | 9 => ⟨((714837767/295147905179352825856), (648816721/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-1050808891/4722366482869645213696), (605891789/4722366482869645213696)), (3/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-19907505/4722366482869645213696), (-1463062679/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((906239419/604462909807314587353088), (167547043/1208925819614629174706176)), (7/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((71/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((29081600/449710249), (-45841920/449710249)), 0, by norm_num⟩
  | 1 => ⟨((627871085363200/202239308055642001), (1333156380672000/202239308055642001)), 0, by norm_num⟩
  | 2 => ⟨((-959576117/2199023255552), (-60371013/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((594890691/35184372088832), (-180015645/8796093022208)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((34930665/70368744177664), (107205703/70368744177664)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-1687943353/18014398509481984), (-431616473/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((306304877/72057594037927936), (-288303265/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((306582423/4611686018427387904), (797879931/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1459937433/73786976294838206464), (-287766829/36893488147419103232)), (7/18446744073709551616), by norm_num⟩
  | 9 => ⟨((612313235/590295810358705651712), (-892821909/1180591620717411303424)), (19/590295810358705651712), by norm_num⟩
  | 10 => ⟨((94542179/18889465931478580854784), (1460565659/18889465931478580854784)), (13/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-1239990809/302231454903657293676544), (-169627405/75557863725914323419136)), (35/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1194815561/4835703278458516698824704), (-660183559/4835703278458516698824704)), (47/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((71/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((71/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((71/16), (17907/2560)))⁻¹=value ((29081600/449710249), (-45841920/449710249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((29081600/449710249), (-45841920/449710249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13797859/4398046511104), (643854789/2199023255552)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-623012251/8796093022208), (-485997175/17592186044416)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((590951063/70368744177664), (-632361975/70368744177664)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((382566551/562949953421312), (403693833/281474976710656)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((-401318697/2251799813685248), (110432763/9007199254740992)), (11/9007199254740992), by norm_num⟩
  | 5 => ⟨((393057521/72057594037927936), (-1260887475/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 6 => ⟨((12408125/9007199254740992), (314635351/288230376151711744)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-634619385/4611686018427387904), (753529633/9223372036854775808)), (5/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-178445645/73786976294838206464), (-508075791/36893488147419103232)), (17/73786976294838206464), by norm_num⟩
  | 9 => ⟨((685220225/590295810358705651712), (64132713/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-235736003/4722366482869645213696), (392514931/4722366482869645213696)), (23/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-367874959/75557863725914323419136), (-457448007/75557863725914323419136)), (9/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1395298249/2417851639229258349412352), (-59316621/302231454903657293676544)), (55/2417851639229258349412352), by norm_num⟩
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
  | 0 => ⟨((87/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((11878400/171475683), (-15280640/171475683)), 0, by norm_num⟩
  | 1 => ⟨((15400262041600/9801303286772163), (181509554176000/29403909860316489)), 0, by norm_num⟩
  | 2 => ⟨((-724503797/2199023255552), (-79053269/549755813888)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((313464483/17592186044416), (-682524885/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-208281847/1125899906842624), (318028245/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-791465943/18014398509481984), (-426727485/9007199254740992)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((1047037659/288230376151711744), (-45637413/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 7 => ⟨((-32198135/288230376151711744), (797015839/4611686018427387904)), (5/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-141349835/36893488147419103232), (-202237453/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 9 => ⟨((366682677/590295810358705651712), (246761405/1180591620717411303424)), (37/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-582327663/18889465931478580854784), (772136191/37778931862957161709568)), (3/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((94964213/604462909807314587353088), (-1258180557/604462909807314587353088)), (61/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((52770693/604462909807314587353088), (382474893/4835703278458516698824704)), (39/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((87/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((87/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((87/16), (17907/2560)))⁻¹=value ((11878400/171475683), (-15280640/171475683)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((11878400/171475683), (-15280640/171475683))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((925655353/35184372088832), (703777425/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-1290655017/140737488355328), (343218277/70368744177664)), (3/70368744177664), by norm_num⟩
  | 2 => ⟨((-16712701/140737488355328), (-1096855679/562949953421312)), (7/562949953421312), by norm_num⟩
  | 3 => ⟨((1197093233/4503599627370496), (454795477/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((-449623297/18014398509481984), (451743339/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((-413411785/288230376151711744), (-530180549/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 6 => ⟨((1873721107/4611686018427387904), (75498233/4611686018427387904)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-629187309/36893488147419103232), (163522797/4611686018427387904)), (25/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-703615117/295147905179352825856), (-804708609/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1434772863/4722366482869645213696), (-118268129/1180591620717411303424)), (37/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-39871887/18889465931478580854784), (514042389/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-1218711771/604462909807314587353088), (-154458329/151115727451828646838272)), (51/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((666650933/4835703278458516698824704), (-577637493/4835703278458516698824704)), (41/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((103/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((42188800/592251049), (-45841920/592251049)), 0, by norm_num⟩
  | 1 => ⟨((160793391923200/350761305041600401), (1934015594496000/350761305041600401)), 0, by norm_num⟩
  | 2 => ⟨((-505155265/2199023255552), (-785686277/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((531133927/35184372088832), (-177862591/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-495225711/1125899906842624), (189785083/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-23482393/2251799813685248), (-1478543727/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((564830655/288230376151711744), (609935101/576460752303423488)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1021454011/9223372036854775808), (175961957/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((364184089/147573952589676412928), (-416530529/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 9 => ⟨((616620367/4722366482869645213696), (350126821/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-1218623979/75557863725914323419136), (-104072961/18889465931478580854784)), (53/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((476121745/604462909807314587353088), (-517364515/1208925819614629174706176)), (1/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-222297993/19342813113834066795298816), (884485159/19342813113834066795298816)), (77/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((103/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((103/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((103/16), (17907/2560)))⁻¹=value ((42188800/592251049), (-45841920/592251049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((42188800/592251049), (-45841920/592251049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((963304965/281474976710656), (-86060083/140737488355328)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((-210526987/562949953421312), (682017275/562949953421312)), (9/1125899906842624), by norm_num⟩
  | 2 => ⟨((-217116967/1125899906842624), (-421596089/2251799813685248)), (11/4503599627370496), by norm_num⟩
  | 3 => ⟨((368084473/9007199254740992), (-510719379/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-214402007/288230376151711744), (209135849/36028797018963968)), (21/288230376151711744), by norm_num⟩
  | 5 => ⟨((-674554547/1152921504606846976), (-445695009/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((1217668439/18446744073709551616), (-180580295/4611686018427387904)), (13/9223372036854775808), by norm_num⟩
  | 7 => ⟨((51213261/73786976294838206464), (575188249/73786976294838206464)), (25/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-417494523/590295810358705651712), (-153759789/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((928617961/18889465931478580854784), (-920814529/18889465931478580854784)), (41/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((316080247/151115727451828646838272), (867516985/151115727451828646838272)), (9/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-313964887/604462909807314587353088), (-48685803/1208925819614629174706176)), (15/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((199550849/9671406556917033397649408), (-732077475/19342813113834066795298816)), (3/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((119/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((48742400/683182249), (-45841920/683182249)), 0, by norm_num⟩
  | 1 => ⟨((-137169964236800/466737985348698001), (2234445201408000/466737985348698001)), 0, by norm_num⟩
  | 2 => ⟨((-165073521/1099511627776), (-794463453/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1606693933/140737488355328), (198012331/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-255836225/562949953421312), (749461375/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((181779173/36028797018963968), (-977105495/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((420760801/576460752303423488), (655281349/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1183830441/18446744073709551616), (-296295817/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((834746583/295147905179352825856), (-116592289/73786976294838206464)), (11/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-452196627/9444732965739290427392), (178571203/1180591620717411303424)), (25/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-127190733/37778931862957161709568), (-1058124373/151115727451828646838272)), (57/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((858392083/2417851639229258349412352), (165419121/1208925819614629174706176)), (1/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-1335078025/77371252455336267181195264), (543913225/77371252455336267181195264)), (71/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((119/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((119/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((119/16), (17907/2560)))⁻¹=value ((48742400/683182249), (-45841920/683182249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((48742400/683182249), (-45841920/683182249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((457429649/2251799813685248), (-1230694719/4503599627370496)), (7/2251799813685248), by norm_num⟩
  | 1 => ⟨((254602065/4503599627370496), (576882555/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 2 => ⟨((-587909985/18014398509481984), (-27841977/9007199254740992)), (15/36028797018963968), by norm_num⟩
  | 3 => ⟨((232915093/72057594037927936), (-682835289/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((438207181/1152921504606846976), (854919439/1152921504606846976)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-489392877/4611686018427387904), (-37299615/18446744073709551616)), (19/9223372036854775808), by norm_num⟩
  | 6 => ⟨((437966895/73786976294838206464), (-197587553/18446744073709551616)), (11/36893488147419103232), by norm_num⟩
  | 7 => ⟨((850274967/1180591620717411303424), (1287826113/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-19218351/147573952589676412928), (133393507/9444732965739290427392)), (21/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((83269223/18889465931478580854784), (-880225745/75557863725914323419136)), (39/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((928495145/1208925819614629174706176), (1006681121/1208925819614629174706176)), (17/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-919711173/9671406556917033397649408), (271206305/9671406556917033397649408)), (59/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((214170081/154742504910672534362390528), (-1280587997/154742504910672534362390528)), (95/154742504910672534362390528), by norm_num⟩
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
  | 0 => ⟨((135/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((6144000/87468961), (-15280640/262406883)), 0, by norm_num⟩
  | 1 => ⟨((-53120332595200/68857372245775689), (31294750720000/7650819138419521)), 0, by norm_num⟩
  | 2 => ⟨((-202315561/2199023255552), (-730604525/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((567737107/70368744177664), (444102991/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-825151/2199023255552), (139707713/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((689284181/72057594037927936), (-1101290171/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((7857135/72057594037927936), (1879931411/2305843009213693952)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1017073379/36893488147419103232), (-469635701/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 8 => ⟨((504550251/295147905179352825856), (107992187/1180591620717411303424)), (23/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-592205055/9444732965739290427392), (879516289/18889465931478580854784)), (3/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((255830953/302231454903657293676544), (-1046002707/302231454903657293676544)), (25/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((687062141/9671406556917033397649408), (1413937459/9671406556917033397649408)), (13/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-522391765/77371252455336267181195264), (-14827113/4835703278458516698824704)), (27/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((135/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((135/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((135/16), (17907/2560)))⁻¹=value ((6144000/87468961), (-15280640/262406883)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((6144000/87468961), (-15280640/262406883))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-59239799/36028797018963968), (-139721185/4503599627370496)), (15/36028797018963968), by norm_num⟩
  | 1 => ⟨((892886257/72057594037927936), (243094563/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 2 => ⟨((-447339283/144115188075855872), (260437639/144115188075855872)), (19/288230376151711744), by norm_num⟩
  | 3 => ⟨((17369891/2305843009213693952), (-1556191617/2305843009213693952)), (31/2305843009213693952), by norm_num⟩
  | 4 => ⟨((102915027/1152921504606846976), (124227501/2305843009213693952)), (11/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-905775953/73786976294838206464), (497658495/73786976294838206464)), (27/73786976294838206464), by norm_num⟩
  | 6 => ⟨((16490719/590295810358705651712), (-1997934689/1180591620717411303424)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((766930779/4722366482869645213696), (448302571/4722366482869645213696)), (17/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-634418869/37778931862957161709568), (188330321/18889465931478580854784)), (67/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-20931563/302231454903657293676544), (-578504403/302231454903657293676544)), (1/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((388314589/2417851639229258349412352), (381902137/4835703278458516698824704)), (57/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-502402195/38685626227668133590597632), (728054703/77371252455336267181195264)), (25/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-250761975/1237940039285380274899124224), (-1696602213/1237940039285380274899124224)), (167/1237940039285380274899124224), by norm_num⟩
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
  | 0 => ⟨((151/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((61849600/904366249), (-45841920/904366249)), 0, by norm_num⟩
  | 1 => ⟨((-861945695436800/817878312330330001), (2835304415232000/817878312330330001)), 0, by norm_num⟩
  | 2 => ⟨((-455850879/8796093022208), (-638828183/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((191878933/35184372088832), (64272031/17592186044416)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-39276879/140737488355328), (59848311/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((331691877/36028797018963968), (-271210809/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-285979207/2305843009213693952), (1131565361/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 7 => ⟨((-604806811/73786976294838206464), (-1470142451/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 8 => ⟨((927068759/1180591620717411303424), (279542573/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-1467872001/37778931862957161709568), (35027487/9444732965739290427392)), (47/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((93285643/75557863725914323419136), (-335951569/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-271679449/19342813113834066795298816), (1340484951/19342813113834066795298816)), (89/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-394947411/309485009821345068724781056), (-843576511/309485009821345068724781056)), (43/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((151/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((151/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((151/16), (17907/2560)))⁻¹=value ((61849600/904366249), (-45841920/904366249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((61849600/904366249), (-45841920/904366249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-121421287/72057594037927936), (-293765625/144115188075855872)), (15/288230376151711744), by norm_num⟩
  | 1 => ⟨((1497342477/1152921504606846976), (-80514179/576460752303423488)), (15/576460752303423488), by norm_num⟩
  | 2 => ⟨((-372513783/2305843009213693952), (734700439/2305843009213693952)), (21/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-2611795/72057594037927936), (-1134982081/18446744073709551616)), (37/18446744073709551616), by norm_num⟩
  | 4 => ⟨((1716954593/147573952589676412928), (50916571/147573952589676412928)), (55/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-133441571/147573952589676412928), (403342425/295147905179352825856)), (35/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-25851259/295147905179352825856), (-882144377/4722366482869645213696)), (43/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((1786818185/75557863725914323419136), (183453515/75557863725914323419136)), (23/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-7146257/4722366482869645213696), (619399069/302231454903657293676544)), (47/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-61629461/604462909807314587353088), (-1140399139/4835703278458516698824704)), (23/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((118234625/4835703278458516698824704), (106010907/38685626227668133590597632)), (21/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-815007697/618970019642690137449562112), (1131365885/618970019642690137449562112)), (75/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-419038703/4951760157141521099596496896), (-888024307/4951760157141521099596496896)), (129/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((167/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((68403200/1034619049), (-45841920/1034619049)), 0, by norm_num⟩
  | 1 => ⟨((-1288758070476800/1070436576553664401), (3135734022144000/1070436576553664401)), 0, by norm_num⟩
  | 2 => ⟨((-220768789/8796093022208), (-1086406243/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1003720003/281474976710656), (248181003/70368744177664)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-1765535401/9007199254740992), (-21160491/562949953421312)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((1053828435/144115188075855872), (-446745363/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-399030519/2305843009213693952), (1219669501/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-20445213/147573952589676412928), (-1855971195/147573952589676412928)), (23/147573952589676412928), by norm_num⟩
  | 8 => ⟨((334344515/1180591620717411303424), (974404027/2361183241434822606848)), (21/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-1398141989/75557863725914323419136), (-556701361/75557863725914323419136)), (19/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((936829033/1208925819614629174706176), (-100571737/604462909807314587353088)), (35/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-848409675/38685626227668133590597632), (876920237/38685626227668133590597632)), (63/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((4309371/19342813113834066795298816), (-1529094271/1237940039285380274899124224)), (113/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((167/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((167/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((167/16), (17907/2560)))⁻¹=value ((68403200/1034619049), (-45841920/1034619049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((68403200/1034619049), (-45841920/1034619049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-465144955/2305843009213693952), (-34649039/576460752303423488)), (27/4611686018427387904), by norm_num⟩
  | 1 => ⟨((808675597/9223372036854775808), (-319408727/4611686018427387904)), (29/9223372036854775808), by norm_num⟩
  | 2 => ⟨((76472923/36893488147419103232), (1197405491/36893488147419103232)), (43/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-436087321/73786976294838206464), (-257431097/73786976294838206464)), (5/18446744073709551616), by norm_num⟩
  | 4 => ⟨((624037247/590295810358705651712), (-300043221/590295810358705651712)), (61/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-216460475/9444732965739290427392), (805816885/4722366482869645213696)), (81/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-80706597/4722366482869645213696), (-552252151/37778931862957161709568)), (51/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((1547351815/604462909807314587353088), (-473097939/604462909807314587353088)), (113/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-370060847/4835703278458516698824704), (344702361/1208925819614629174706176)), (59/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-811508491/38685626227668133590597632), (-858634001/38685626227668133590597632)), (59/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((904652677/309485009821345068724781056), (-6123807/9671406556917033397649408)), (55/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-219532095/2475880078570760549798248448), (1311601569/4951760157141521099596496896)), (25/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-81594087/4951760157141521099596496896), (-372917203/19807040628566084398385987584)), (11/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((183/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((24985600/392659683), (-15280640/392659683)), 0, by norm_num⟩
  | 1 => ⟨((-65130374758400/51393875551220163), (381795958784000/154181626653660489)), 0, by norm_num⟩
  | 2 => ⟨((-69167733/8796093022208), (-454948437/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((318484521/140737488355328), (110413129/35184372088832)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1198494113/9007199254740992), (-502689209/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1533195649/288230376151711744), (-117226511/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-353743687/2305843009213693952), (596672619/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((174389323/73786976294838206464), (-1047994867/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((297441835/4722366482869645213696), (321034655/1180591620717411303424)), (23/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-551199399/75557863725914323419136), (-561093965/75557863725914323419136)), (5/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((910546147/2417851639229258349412352), (228048461/2417851639229258349412352)), (17/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-1069028245/77371252455336267181195264), (83693851/19342813113834066795298816)), (57/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((219984181/618970019642690137449562112), (-1006469517/2475880078570760549798248448)), (47/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((183/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((183/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((183/16), (17907/2560)))⁻¹=value ((24985600/392659683), (-15280640/392659683)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((24985600/392659683), (-15280640/392659683))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1119729015/73786976294838206464), (148517595/36893488147419103232)), (45/73786976294838206464), by norm_num⟩
  | 1 => ⟨((485248445/147573952589676412928), (-608191887/73786976294838206464)), (13/36893488147419103232), by norm_num⟩
  | 2 => ⟨((214085707/147573952589676412928), (682019857/295147905179352825856)), (5/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-1423693319/2361183241434822606848), (-22016415/590295810358705651712)), (39/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((318276303/4722366482869645213696), (-198408655/2361183241434822606848)), (31/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((353073145/75557863725914323419136), (148610815/9444732965739290427392)), (85/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-1276136563/604462909807314587353088), (-407878027/604462909807314587353088)), (109/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((1028699689/4835703278458516698824704), (-408697065/2417851639229258349412352)), (31/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((106284641/38685626227668133590597632), (592638221/19342813113834066795298816)), (133/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-445986075/154742504910672534362390528), (-117396771/77371252455336267181195264)), (17/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((699636751/2475880078570760549798248448), (-200360685/1237940039285380274899124224)), (129/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-11642325/9903520314283042199192993792), (1226171115/39614081257132168796771975168)), (239/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-743499883/316912650057057350374175801344), (-495793321/316912650057057350374175801344)), (213/316912650057057350374175801344), by norm_num⟩
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
  | 0 => ⟨((199/16), (17907/2560)), 0, by norm_num⟩
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
  | 0 => ⟨((81510400/1334446249), (-45841920/1334446249)), 0, by norm_num⟩
  | 1 => ⟨((-2271231839436800/1780746791470170001), (3736593235968000/1780746791470170001)), 0, by norm_num⟩
  | 2 => ⟨((51216501/17592186044416), (-94549525/1099511627776)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((195360827/140737488355328), (376654141/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-397953691/4503599627370496), (-260728545/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((532231693/144115188075855872), (72158811/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-269992845/2305843009213693952), (257277365/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((772643753/295147905179352825856), (-1096479065/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-152438311/9444732965739290427392), (187034765/1180591620717411303424)), (25/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-336720669/151115727451828646838272), (-386528249/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((47124139/302231454903657293676544), (570438531/4835703278458516698824704)), (1/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-525207913/77371252455336267181195264), (-143070541/154742504910672534362390528)), (25/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((552609399/2475880078570760549798248448), (-218765447/2475880078570760549798248448)), (77/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((199/16), (17907/2560)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((199/16), (17907/2560)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((199/16), (17907/2560)))⁻¹=value ((81510400/1334446249), (-45841920/1334446249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((81510400/1334446249), (-45841920/1334446249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-58191101/73786976294838206464), (905747805/1180591620717411303424)), (35/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-168584913/2361183241434822606848), (-771403011/1180591620717411303424)), (85/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((856621225/4722366482869645213696), (507469/4611686018427387904)), (17/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-860247247/18889465931478580854784), (171800623/9444732965739290427392)), (35/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((174429577/75557863725914323419136), (-1327662427/151115727451828646838272)), (115/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((68482871/75557863725914323419136), (167520771/151115727451828646838272)), (41/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-1923237011/9671406556917033397649408), (125923983/9671406556917033397649408)), (53/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((504338707/38685626227668133590597632), (-829653135/38685626227668133590597632)), (125/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((368456491/309485009821345068724781056), (410994963/154742504910672534362390528)), (17/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-1535787257/4951760157141521099596496896), (-269073437/4951760157141521099596496896)), (141/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((875715495/39614081257132168796771975168), (-230368033/9903520314283042199192993792)), (137/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((113440977/158456325028528675187087900672), (957446103/316912650057057350374175801344)), (129/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-686566695/2535301200456458802993406410752), (-481391049/5070602400912917605986812821504)), (465/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-199572833/4398046511104), (569853151/2199023255552)), (123/549755813888), by norm_num⟩
  | 1 => ⟨((-1013984733/4398046511104), (60603347/274877906944)), (1017/2199023255552), by norm_num⟩
  | 2 => ⟨((-824012573/4398046511104), (28835809/1099511627776)), (273/549755813888), by norm_num⟩
  | 3 => ⟨((-286325595/4398046511104), (-583979537/17592186044416)), (1607/4398046511104), by norm_num⟩
  | 4 => ⟨((-352339115/35184372088832), (-636067433/35184372088832)), (14477/70368744177664), by norm_num⟩
  | 5 => ⟨((84113803/281474976710656), (-1281804263/281474976710656)), (26511/281474976710656), by norm_num⟩
  | 6 => ⟨((264344245/562949953421312), (-757974419/1125899906842624)), (40991/1125899906842624), by norm_num⟩
  | 7 => ⟨((1005550169/9007199254740992), (-488837551/9007199254740992)), (27473/2251799813685248), by norm_num⟩
  | 8 => ⟨((1169115989/72057594037927936), (19757243/72057594037927936)), (260387/72057594037927936), by norm_num⟩
  | 9 => ⟨((30607915/18014398509481984), (116526415/144115188075855872)), (276827/288230376151711744), by norm_num⟩
  | 10 => ⟨((76810837/576460752303423488), (675597649/4611686018427387904)), (534727/2305843009213693952), by norm_num⟩
  | 11 => ⟨((8220875/1152921504606846976), (329327911/18446744073709551616)), (3791715/73786976294838206464), by norm_num⟩
  | 12 => ⟨((11407833/147573952589676412928), (2046788321/1180591620717411303424)), (6221577/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-199572833/4398046511104), (569853151/2199023255552)), (985/4398046511104), by norm_num⟩
  | 1 => ⟨((-1013984733/4398046511104), (60603347/274877906944)), (2035/4398046511104), by norm_num⟩
  | 2 => ⟨((-824012573/4398046511104), (28835809/1099511627776)), (4369/8796093022208), by norm_num⟩
  | 3 => ⟨((-286325595/4398046511104), (-583979537/17592186044416)), (6429/17592186044416), by norm_num⟩
  | 4 => ⟨((-352339115/35184372088832), (-636067433/35184372088832)), (905/4398046511104), by norm_num⟩
  | 5 => ⟨((84113803/281474976710656), (-1281804263/281474976710656)), (26523/281474976710656), by norm_num⟩
  | 6 => ⟨((264344245/562949953421312), (-757974419/1125899906842624)), (41037/1125899906842624), by norm_num⟩
  | 7 => ⟨((1005550169/9007199254740992), (-488837551/9007199254740992)), (110253/9007199254740992), by norm_num⟩
  | 8 => ⟨((1169115989/72057594037927936), (19757243/72057594037927936)), (131635/36028797018963968), by norm_num⟩
  | 9 => ⟨((30607915/18014398509481984), (116526415/144115188075855872)), (576713/576460752303423488), by norm_num⟩
  | 10 => ⟨((76810837/576460752303423488), (675597649/4611686018427387904)), (626961/2305843009213693952), by norm_num⟩
  | 11 => ⟨((8220875/1152921504606846976), (329327911/18446744073709551616)), (6743195/73786976294838206464), by norm_num⟩
  | 12 => ⟨((11407833/147573952589676412928), (2046788321/1180591620717411303424)), (59666819/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile043Gamma
