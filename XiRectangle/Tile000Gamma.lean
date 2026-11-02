/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile000Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (141/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (141/640))
  have he : value ((3/4), (141/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/293114281), (-180480/293114281)), 0, by norm_num⟩
  | 1 => ⟨((-240086645964800/85915981726146961), (3954966528000/85915981726146961)), 0, by norm_num⟩
  | 2 => ⟨((58796525845/562949953421312), (-5812016377/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-17579236415/4503599627370496), (9269208689/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((336355731497/2305843009213693952), (-13858618697/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-402205650525/73786976294838206464), (77699581/288230376151711744)), (3/73786976294838206464), by norm_num⟩
  | 6 => ⟨((480914612219/2361183241434822606848), (-27755755815/2361183241434822606848)), (5/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-287493630173/37778931862957161709568), (2371170717/4722366482869645213696)), (1/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((343707405947/1208925819614629174706176), (-25523093137/1208925819614629174706176)), (3/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-205442332661/19342813113834066795298816), (8479084189/9671406556917033397649408)), (1/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((491158108071/1237940039285380274899124224), (-44617983061/1237940039285380274899124224)), (11/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-293537104415/19807040628566084398385987584), (29104957843/19807040628566084398385987584)), (1/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((175418319615/316912650057057350374175801344), (-18853314917/316912650057057350374175801344)), (11/633825300114114700748351602688), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (141/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (141/1280)))⁻¹=value ((21913600/293114281), (-180480/293114281)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/293114281), (-180480/293114281))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((356437096647/137438953472), (1131919059/137438953472)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((10956800/293114281), (-90240/293114281)), 0, by norm_num⟩
  | 2 => ⟨((-60021661491200/85915981726146961), (988741632000/85915981726146961)), 0, by norm_num⟩
  | 3 => ⟨((313581471173/18014398509481984), (-7749355169/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-17579236415/36028797018963968), (9269208689/576460752303423488)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((134542292599/9223372036854775808), (-5543447479/9223372036854775808)), (3/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-134068550175/295147905179352825856), (13260728491/590295810358705651712)), (3/590295810358705651712), by norm_num⟩
  | 7 => ⟨((274808349839/18889465931478580854784), (-7930215947/9444732965739290427392)), (1/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-287493630173/604462909807314587353088), (2371170717/75557863725914323419136)), (1/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((305517694175/19342813113834066795298816), (-5671798475/4835703278458516698824704)), (3/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-164353866129/309485009821345068724781056), (27133069405/618970019642690137449562112)), (7/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((357205896779/19807040628566084398385987584), (-16224721113/9903520314283042199192993792)), (9/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-391382805887/633825300114114700748351602688), (38806610457/633825300114114700748351602688)), (3/158456325028528675187087900672), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (3/20480)), 0, by norm_num⟩
  | 45 => ⟨((107567591513/4080638361600), (-5961/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-51806906502799/1915179604377600), (126795393113/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((30448053079/1099511627776), (-3893764539/17592186044416)), (1/17592186044416), by norm_num⟩
  | 42 => ⟨((-249380452081/8796093022208), (998216023/4398046511104)), (1/17592186044416), by norm_num⟩
  | 41 => ⟨((255439089653/8796093022208), (-4088931193/17592186044416)), (1/17592186044416), by norm_num⟩
  | 40 => ⟨((-261796225535/8796093022208), (4188116801/17592186044416)), (1/17592186044416), by norm_num⟩
  | 39 => ⟨((134238686437/4398046511104), (-4291924221/17592186044416)), (1/17592186044416), by norm_num⟩
  | 38 => ⟨((-17219276669/549755813888), (2200475697/8796093022208)), (1/8796093022208), by norm_num⟩
  | 37 => ⟨((70729423835/2199023255552), (-1128913245/4398046511104)), (1/8796093022208), by norm_num⟩
  | 36 => ⟨((-290736557069/8796093022208), (1159123341/4398046511104)), (1/8796093022208), by norm_num⟩
  | 35 => ⟨((298999949301/8796093022208), (-4652325/17179869184)), (1/8796093022208), by norm_num⟩
  | 34 => ⟨((-307746898037/8796093022208), (2449339873/8796093022208)), (1/8796093022208), by norm_num⟩
  | 33 => ⟨((19813820983/549755813888), (-315076261/1099511627776)), (1/8796093022208), by norm_num⟩
  | 32 => ⟨((-326871833215/8796093022208), (1298076905/4398046511104)), (1/8796093022208), by norm_num⟩
  | 31 => ⟨((337354472427/8796093022208), (-1338183723/4398046511104)), (1/4398046511104), by norm_num⟩
  | 30 => ⟨((-174265946355/4398046511104), (2761698009/8796093022208)), (1/8796093022208), by norm_num⟩
  | 29 => ⟨((180237776247/4398046511104), (-1426325737/4398046511104)), (1/8796093022208), by norm_num⟩
  | 28 => ⟨((-373267059859/8796093022208), (2949802825/8796093022208)), (1/8796093022208), by norm_num⟩
  | 27 => ⟨((48375005169/1099511627776), (-3053808249/8796093022208)), (1/8796093022208), by norm_num⟩
  | 26 => ⟨((-401782439615/8796093022208), (3165419997/8796093022208)), (1/8796093022208), by norm_num⟩
  | 25 => ⟨((417739359213/8796093022208), (-3285504647/8796093022208)), (1/8796093022208), by norm_num⟩
  | 24 => ⟨((-435016619617/8796093022208), (3415065687/8796093022208)), (1/8796093022208), by norm_num⟩
  | 23 => ⟨((226892614641/4398046511104), (-3555271683/8796093022208)), (1/8796093022208), by norm_num⟩
  | 22 => ⟨((-474247072067/8796093022208), (926872927/2199023255552)), (1/8796093022208), by norm_num⟩
  | 21 => ⟨((31040137971/549755813888), (-1936670149/4398046511104)), (1/8796093022208), by norm_num⟩
  | 20 => ⟨((-130314586561/2199023255552), (4054735091/8796093022208)), (1/8796093022208), by norm_num⟩
  | 19 => ⟨((34277705991/549755813888), (-66468305/137438953472)), (1/4398046511104), by norm_num⟩
  | 18 => ⟨((-144655381299/2199023255552), (2236910377/4398046511104)), (1/4398046511104), by norm_num⟩
  | 17 => ⟨((306158264685/4398046511104), (-1179414951/2199023255552)), (1/4398046511104), by norm_num⟩
  | 16 => ⟨((-325090757253/4398046511104), (2494823427/4398046511104)), (1/4398046511104), by norm_num⟩
  | 15 => ⟨((86630281707/1099511627776), (-2647480639/4398046511104)), (1/4398046511104), by norm_num⟩
  | 14 => ⟨((-370979074451/4398046511104), (2820069035/4398046511104)), (1/4398046511104), by norm_num⟩
  | 13 => ⟨((399155608973/4398046511104), (-3016771555/4398046511104)), (1/4398046511104), by norm_num⟩
  | 12 => ⟨((-431969573257/4398046511104), (3243031899/4398046511104)), (1/4398046511104), by norm_num⟩
  | 11 => ⟨((235335045349/2199023255552), (-1753034595/2199023255552)), (1/4398046511104), by norm_num⟩
  | 10 => ⟨((-516999824401/4398046511104), (1907833869/2199023255552)), (1/4398046511104), by norm_num⟩
  | 9 => ⟨((71683231035/549755813888), (-261589413/274877906944)), (1/2199023255552), by norm_num⟩
  | 8 => ⟨((-628721913/4294967296), (579356271/549755813888)), (1/2199023255552), by norm_num⟩
  | 7 => ⟨((45867858141/274877906944), (-40569489/34359738368)), (1/2199023255552), by norm_num⟩
  | 6 => ⟨((-106671890951/549755813888), (2952295259/2199023255552)), (1/2199023255552), by norm_num⟩
  | 5 => ⟨((254893876843/1099511627776), (-3422004813/2199023255552)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((-316684653763/1099511627776), (1017797967/549755813888)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((104611484333/274877906944), (-4910673/2147483648)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-77298723795/137438953472), (1646699369/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((37529485265/34359738368), (-18741375/4294967296)), (1/274877906944), by norm_num⟩
  | 0 => ⟨((-12312297873/68719476736), (18110704945/2199023255552)), (1/1099511627776), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (141/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (141/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (141/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((356437096647/137438953472), (1131919059/137438953472)), (1/137438953472), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (141/1280))) (z:=((-21/128), (141/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((356437096647/137438953472), (1131919059/137438953472))) (r:=(1/137438953472)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((286812683211/8589934592), (841206747/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((122184623451/68719476736), (1174231877/274877906944)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((832909469260800/85915981726146961), (-7107028995360/85915981726146961)), 0, by norm_num⟩
  | 3 => ⟨((-281786705501/2251799813685248), (150105511/70368744177664)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((174369972001/72057594037927936), (-4454003127/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-258649799261/4611686018427387904), (17602457639/9223372036854775808)), (7/2305843009213693952), by norm_num⟩
  | 6 => ⟨((425813722019/295147905179352825856), (-18097708733/295147905179352825856)), (45/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-375144487861/9444732965739290427392), (9560113127/4722366482869645213696)), (51/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((5416902459/4722366482869645213696), (-10301386663/151115727451828646838272)), (59/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-331929317031/9671406556917033397649408), (11266728453/4835703278458516698824704)), (9/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((326591088401/309485009821345068724781056), (-24933022471/309485009821345068724781056)), (47/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-164180821557/4951760157141521099596496896), (3480687743/1237940039285380274899124224)), (115/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((335982965993/316912650057057350374175801344), (-31334614097/316912650057057350374175801344)), (151/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((171922308043/8589934592), (4837184011/17179869184)), (5/17179869184), by norm_num⟩
  | 1 => ⟨((87824885083/68719476736), (1174231877/274877906944)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((832909469260800/85915981726146961), (-7107028995360/85915981726146961)), 0, by norm_num⟩
  | 3 => ⟨((-281786705501/2251799813685248), (150105511/70368744177664)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((174369972001/72057594037927936), (-4454003127/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-258649799261/4611686018427387904), (17602457639/9223372036854775808)), (7/2305843009213693952), by norm_num⟩
  | 6 => ⟨((425813722019/295147905179352825856), (-18097708733/295147905179352825856)), (45/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-375144487861/9444732965739290427392), (9560113127/4722366482869645213696)), (51/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((5416902459/4722366482869645213696), (-10301386663/151115727451828646838272)), (59/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-331929317031/9671406556917033397649408), (11266728453/4835703278458516698824704)), (9/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((326591088401/309485009821345068724781056), (-24933022471/309485009821345068724781056)), (47/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-164180821557/4951760157141521099596496896), (3480687743/1237940039285380274899124224)), (115/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((335982965993/316912650057057350374175801344), (-31334614097/316912650057057350374175801344)), (151/316912650057057350374175801344), by norm_num⟩
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
  | 0 => ⟨((505191801235/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((505191801235/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((359631859875/17179869184), (4837184011/17179869184)), (3/8589934592), by norm_num⟩
  | 1 => ⟨((87824885083/68719476736), (1174231877/274877906944)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((832909469260800/85915981726146961), (-7107028995360/85915981726146961)), 0, by norm_num⟩
  | 3 => ⟨((-281786705501/2251799813685248), (150105511/70368744177664)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((174369972001/72057594037927936), (-4454003127/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-258649799261/4611686018427387904), (17602457639/9223372036854775808)), (7/2305843009213693952), by norm_num⟩
  | 6 => ⟨((425813722019/295147905179352825856), (-18097708733/295147905179352825856)), (45/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-375144487861/9444732965739290427392), (9560113127/4722366482869645213696)), (51/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((5416902459/4722366482869645213696), (-10301386663/151115727451828646838272)), (59/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-331929317031/9671406556917033397649408), (11266728453/4835703278458516698824704)), (9/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((326591088401/309485009821345068724781056), (-24933022471/309485009821345068724781056)), (47/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-164180821557/4951760157141521099596496896), (3480687743/1237940039285380274899124224)), (115/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((335982965993/316912650057057350374175801344), (-31334614097/316912650057057350374175801344)), (151/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((480173291929600/85915981726146961), (-7909933056000/85915981726146961)), 0, by norm_num⟩
  | 1 => ⟨((-58796525845/140737488355328), (5812016377/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((52737709245/2251799813685248), (-13903813033/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((-336355731497/288230376151711744), (13858618697/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((125689265789/2305843009213693952), (-388497905/144115188075855872)), (3/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-90171489791/36893488147419103232), (20816816861/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 6 => ⟨((251556926401/2361183241434822606848), (-16598195019/2361183241434822606848)), (5/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-171853702973/37778931862957161709568), (25523093137/75557863725914323419136)), (5/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((462245248487/2417851639229258349412352), (-19077939425/1208925819614629174706176)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-38371727193/4835703278458516698824704), (27886239413/38685626227668133590597632)), (3/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((403613518571/1237940039285380274899124224), (-20009658517/618970019642690137449562112)), (9/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-263127479423/19807040628566084398385987584), (28279972375/19807040628566084398385987584)), (7/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((340675145417/633825300114114700748351602688), (-19727614367/316912650057057350374175801344)), (5/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((58796525845/140737488355328), (-5812016377/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-52737709245/1125899906842624), (13903813033/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((252266798623/72057594037927936), (-20787928045/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 3 => ⟨((-125689265789/576460752303423488), (388497905/36028797018963968)), (3/2305843009213693952), by norm_num⟩
  | 4 => ⟨((450857448955/36893488147419103232), (-6505255269/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-377335389601/590295810358705651712), (1556080783/36893488147419103232)), (1/147573952589676412928), by norm_num⟩
  | 6 => ⟨((300743980203/9444732965739290427392), (-22332706495/9444732965739290427392)), (1/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-231122624243/151115727451828646838272), (19077939425/151115727451828646838272)), (3/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((345345544737/4835703278458516698824704), (-31372019339/4835703278458516698824704)), (3/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-252258449107/77371252455336267181195264), (12506036573/38685626227668133590597632)), (5/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((180900142103/1237940039285380274899124224), (-1215155063/77371252455336267181195264)), (1/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-255506359063/39614081257132168796771975168), (29591421551/39614081257132168796771975168)), (7/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((22264390245/79228162514264337593543950336), (-22116418321/633825300114114700748351602688)), (5/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17579236415/562949953421312), (-9269208689/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((-336355731497/72057594037927936), (13858618697/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((125689265789/288230376151711744), (-24863865919/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-300571632637/9223372036854775808), (2168418423/1152921504606846976)), (3/9223372036854775808), by norm_num⟩
  | 4 => ⟨((314446158001/147573952589676412928), (-20747743773/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-300743980203/2361183241434822606848), (22332706495/2361183241434822606848)), (1/590295810358705651712), by norm_num⟩
  | 6 => ⟨((269643061617/37778931862957161709568), (-5564398999/9444732965739290427392)), (1/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-115115181579/302231454903657293676544), (41829359119/1208925819614629174706176)), (7/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((94596918415/4835703278458516698824704), (-37518109719/19342813113834066795298816)), (7/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-150750118419/154742504910672534362390528), (32404135013/309485009821345068724781056)), (3/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((117107081237/2475880078570760549798248448), (-54250939509/9903520314283042199192993792)), (11/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-22264390245/9903520314283042199192993792), (22116418321/79228162514264337593543950336)), (9/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((266049948307/2535301200456458802993406410752), (-17631231067/1267650600228229401496703205376)), (1/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((336355731497/144115188075855872), (-13858618697/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 1 => ⟨((-125689265789/288230376151711744), (388497905/18014398509481984)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((450857448955/9223372036854775808), (-6505255269/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-314446158001/73786976294838206464), (20747743773/73786976294838206464)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((187964987627/590295810358705651712), (-13957941559/590295810358705651712)), (5/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-404464592425/18889465931478580854784), (16693196997/9444732965739290427392)), (3/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((402903135527/302231454903657293676544), (-36600689229/302231454903657293676544)), (7/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-94596918415/1208925819614629174706176), (37518109719/4835703278458516698824704)), (7/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((339187766443/77371252455336267181195264), (-36454651889/77371252455336267181195264)), (7/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-73191925773/309485009821345068724781056), (33906837193/1237940039285380274899124224)), (7/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((244908292695/19807040628566084398385987584), (-30410075191/19807040628566084398385987584)), (3/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-99768730615/158456325028528675187087900672), (3305855825/39614081257132168796771975168)), (11/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((317896375881/10141204801825835211973625643008), (-22400660441/5070602400912917605986812821504)), (9/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((402205650525/2305843009213693952), (-77699581/9007199254740992)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-90171489791/2305843009213693952), (20816816861/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 2 => ⟨((377335389601/73786976294838206464), (-1556080783/4611686018427387904)), (1/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-300743980203/590295810358705651712), (22332706495/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 4 => ⟨((202232296213/4722366482869645213696), (-33386393993/9444732965739290427392)), (3/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-60435470329/18889465931478580854784), (43920827075/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((132435685781/604462909807314587353088), (-26262676803/1208925819614629174706176)), (5/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-135675106577/9671406556917033397649408), (3645465189/2417851639229258349412352)), (3/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((263490932783/309485009821345068724781056), (-15258076737/154742504910672534362390528)), (3/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-244908292695/4951760157141521099596496896), (30410075191/4951760157141521099596496896)), (7/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((219491207353/79228162514264337593543950336), (-7272882815/19807040628566084398385987584)), (11/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-381475651057/2535301200456458802993406410752), (26880792529/1267650600228229401496703205376)), (11/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((322847076187/40564819207303340847894502572032), (-48213950447/40564819207303340847894502572032)), (5/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((480914612219/36893488147419103232), (-27755755815/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-251556926401/73786976294838206464), (16598195019/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 2 => ⟨((300743980203/590295810358705651712), (-22332706495/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 3 => ⟨((-269643061617/4722366482869645213696), (5564398999/1180591620717411303424)), (5/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((402903135527/75557863725914323419136), (-36600689229/75557863725914323419136)), (7/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-132435685781/302231454903657293676544), (26262676803/604462909807314587353088)), (5/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((39571906085/1208925819614629174706176), (-34024341763/9671406556917033397649408)), (7/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-351321243711/154742504910672534362390528), (5086025579/19342813113834066795298816)), (1/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((183681219521/1237940039285380274899124224), (-45615112787/2475880078570760549798248448)), (9/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-182909339461/19807040628566084398385987584), (24242942717/19807040628566084398385987584)), (11/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((349686013469/633825300114114700748351602688), (-24640726485/316912650057057350374175801344)), (5/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-322847076187/10141204801825835211973625643008), (48213950447/10141204801825835211973625643008)), (5/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((289281300557/162259276829213363391578010288128), (-22819945743/81129638414606681695789005144064)), (5/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((287493630173/295147905179352825856), (-2371170717/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 1 => ⟨((-171853702973/590295810358705651712), (25523093137/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 2 => ⟨((231122624243/4722366482869645213696), (-19077939425/4722366482869645213696)), (7/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-115115181579/18889465931478580854784), (41829359119/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((94596918415/151115727451828646838272), (-37518109719/604462909807314587353088)), (1/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-135675106577/2417851639229258349412352), (29163721511/4835703278458516698824704)), (3/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((351321243711/77371252455336267181195264), (-5086025579/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-419842787477/1237940039285380274899124224), (26065778735/618970019642690137449562112)), (11/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((470338301471/19807040628566084398385987584), (-62338995557/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((-124887861953/79228162514264337593543950336), (8800259459/39614081257132168796771975168)), (1/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((253665559861/2535301200456458802993406410752), (-37882389637/2535301200456458802993406410752)), (1/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-247955400477/40564819207303340847894502572032), (9779976747/10141204801825835211973625643008)), (9/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((469005543307/1298074214633706907132624082305024), (-38979496657/649037107316853453566312041152512)), (17/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((343707405947/4722366482869645213696), (-25523093137/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((-231122624243/9444732965739290427392), (19077939425/9444732965739290427392)), (9/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((345345544737/75557863725914323419136), (-31372019339/75557863725914323419136)), (3/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-94596918415/151115727451828646838272), (37518109719/604462909807314587353088)), (1/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((339187766443/4835703278458516698824704), (-18227325945/2417851639229258349412352)), (1/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-263490932783/38685626227668133590597632), (15258076737/19342813113834066795298816)), (7/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((183681219521/309485009821345068724781056), (-45615112787/618970019642690137449562112)), (5/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-470338301471/9903520314283042199192993792), (62338995557/9903520314283042199192993792)), (13/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((280997689395/79228162514264337593543950336), (-39601167565/79228162514264337593543950336)), (9/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((-158540974913/633825300114114700748351602688), (23676493523/633825300114114700748351602688)), (5/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((42617334457/2535301200456458802993406410752), (-53789872109/20282409603651670423947251286016)), (3/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-43969269685/40564819207303340847894502572032), (29234622493/162259276829213363391578010288128)), (13/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((350154547219/5192296858534827628530496329220096), (-61170964111/5192296858534827628530496329220096)), (13/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((205442332661/37778931862957161709568), (-8479084189/18889465931478580854784)), (1/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-38371727193/18889465931478580854784), (27886239413/151115727451828646838272)), (7/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((252258449107/604462909807314587353088), (-12506036573/302231454903657293676544)), (3/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-150750118419/2417851639229258349412352), (32404135013/4835703278458516698824704)), (7/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((73191925773/9671406556917033397649408), (-16953418597/19342813113834066795298816)), (1/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((-122454146347/154742504910672534362390528), (30410075191/309485009821345068724781056)), (1/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((365818678921/4951760157141521099596496896), (-24242942717/2475880078570760549798248448)), (11/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((-124887861953/19807040628566084398385987584), (35201037835/39614081257132168796771975168)), (1/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((317081949827/633825300114114700748351602688), (-23676493523/316912650057057350374175801344)), (11/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((-378820750729/10141204801825835211973625643008), (59766524565/10141204801825835211973625643008)), (13/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((429921748031/162259276829213363391578010288128), (-35731205269/81129638414606681695789005144064)), (1/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((-466872729625/2596148429267413814265248164610048), (40780642741/1298074214633706907132624082305024)), (9/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((243976493489/20769187434139310514121985316880384), (-11173916523/5192296858534827628530496329220096)), (5/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((491158108071/1208925819614629174706176), (-44617983061/1208925819614629174706176)), (11/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((-403613518571/2417851639229258349412352), (20009658517/1208925819614629174706176)), (5/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((180900142103/4835703278458516698824704), (-1215155063/302231454903657293676544)), (5/4835703278458516698824704), by norm_num⟩
  | 3 => ⟨((-117107081237/19342813113834066795298816), (27125469755/38685626227668133590597632)), (3/19342813113834066795298816), by norm_num⟩
  | 4 => ⟨((122454146347/154742504910672534362390528), (-3801259399/38685626227668133590597632)), (1/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-438982414705/4951760157141521099596496896), (7272882815/618970019642690137449562112)), (15/4951760157141521099596496896), by norm_num⟩
  | 6 => ⟨((87421503367/9903520314283042199192993792), (-24640726485/19807040628566084398385987584)), (11/39614081257132168796771975168), by norm_num⟩
  | 7 => ⟨((-253665559861/316912650057057350374175801344), (37882389637/316912650057057350374175801344)), (9/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((42617334457/633825300114114700748351602688), (-13447468027/1267650600228229401496703205376)), (13/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-6717527313/1267650600228229401496703205376), (35731205269/40564819207303340847894502572032)), (1/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((128390000647/324518553658426726783156020576256), (-44858707015/649037107316853453566312041152512)), (5/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-146385896093/5192296858534827628530496329220096), (53634799311/10384593717069655257060992658440192)), (3/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((320539565947/166153499473114484112975882535043072), (-61454441853/166153499473114484112975882535043072)), (7/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/879342843), (-15040/293114281)), 0, by norm_num⟩
  | 1 => ⟨((-60021661491200/257747945178440883), (329580544000/85915981726146961)), 0, by norm_num⟩
  | 2 => ⟨((313581471173/36028797018963968), (-7749355169/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((-375023710187/1152921504606846976), (12358944919/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((448474308663/36893488147419103232), (-18478158263/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-134068550175/295147905179352825856), (13260728491/590295810358705651712)), (3/590295810358705651712), by norm_num⟩
  | 6 => ⟨((320609741479/18889465931478580854784), (-9251918605/9444732965739290427392)), (1/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-383324840231/604462909807314587353088), (790390239/18889465931478580854784)), (3/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((458276541263/19342813113834066795298816), (-34030790849/19342813113834066795298816)), (9/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-273923110215/309485009821345068724781056), (22610891171/309485009821345068724781056)), (3/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((163719369357/4951760157141521099596496896), (-29745322041/9903520314283042199192993792)), (1/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-391382805887/316912650057057350374175801344), (38806610457/316912650057057350374175801344)), (3/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((58472773205/1267650600228229401496703205376), (-50275506445/10141204801825835211973625643008)), (15/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179869446149/8589934592), (2418151247/8589934592)), (7/17179869184), by norm_num⟩
  | 1 => ⟨((351235529623/274877906944), (1175286331/274877906944)), (3/274877906944), by norm_num⟩
  | 2 => ⟨((341399892177/35184372088832), (-2918043145/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-282519173685/2251799813685248), (1206878729/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((175245898385/72057594037927936), (-140315415/2251799813685248)), (13/144115188075855872), by norm_num⟩
  | 5 => ⟨((-521489240715/9223372036854775808), (8904828261/4611686018427387904)), (29/9223372036854775808), by norm_num⟩
  | 6 => ⟨((215411624615/147573952589676412928), (-18386831189/295147905179352825856)), (23/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-190566969245/4722366482869645213696), (9757710687/4722366482869645213696)), (13/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((353842328333/302231454903657293676544), (-21134504433/302231454903657293676544)), (15/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-340489414225/9671406556917033397649408), (23240047255/9671406556917033397649408)), (73/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((168411774493/154742504910672534362390528), (-25862563785/309485009821345068724781056)), (95/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-170296177899/4951760157141521099596496896), (29058208521/9903520314283042199192993792)), (29/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((175300579647/158456325028528675187087900672), (-32905723673/316912650057057350374175801344)), (153/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-334486902585/288230376151711744), (8265978847/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 1 => ⟨((300018968149/2305843009213693952), (-9887155935/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-179389723465/18446744073709551616), (7391263305/18446744073709551616)), (3/36893488147419103232), by norm_num⟩
  | 3 => ⟨((44689516725/73786976294838206464), (-17680971321/590295810358705651712)), (3/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-320609741479/9444732965739290427392), (9251918605/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((268327388161/151115727451828646838272), (-17704741353/151115727451828646838272)), (1/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-106931192961/1208925819614629174706176), (7940517865/1208925819614629174706176)), (7/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((328707732257/77371252455336267181195264), (-6783267351/19342813113834066795298816)), (5/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-245579054035/1237940039285380274899124224), (11154495765/618970019642690137449562112)), (5/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((358767572063/39614081257132168796771975168), (-8893181563/9903520314283042199192993792)), (1/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-128640101051/316912650057057350374175801344), (27651528545/633825300114114700748351602688)), (7/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((181693410889/10141204801825835211973625643008), (-42085577317/20282409603651670423947251286016)), (11/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-253319284565/324518553658426726783156020576256), (7863615403/81129638414606681695789005144064)), (1/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359738872361/17179869184), (4836302987/17179869184)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((87808891347/68719476736), (36727661/8589934592)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((170699775009/17592186044416), (-2918029047/35184372088832)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-282517809869/2251799813685248), (1206861867/562949953421312)), (7/2251799813685248), by norm_num⟩
  | 4 => ⟨((175243452327/72057594037927936), (-4489952107/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 5 => ⟨((-521472863311/9223372036854775808), (8904287955/4611686018427387904)), (15/4611686018427387904), by norm_num⟩
  | 6 => ⟨((215398571491/147573952589676412928), (-9192446293/147573952589676412928)), (47/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-190546906517/4722366482869645213696), (1219506827/590295810358705651712)), (53/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((353782372509/302231454903657293676544), (-10564528951/151115727451828646838272)), (61/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-170200912243/4835703278458516698824704), (23231362507/9671406556917033397649408)), (37/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((336697923887/309485009821345068724781056), (-12924531031/154742504910672534362390528)), (3/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-170207460413/4951760157141521099596496896), (29037658923/9903520314283042199192993792)), (117/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((87588444295/79228162514264337593543950336), (-32875006425/316912650057057350374175801344)), (77/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((136677884545/73786976294838206464), (-11262877417/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-6384216675/18446744073709551616), (20206824367/1180591620717411303424)), (1/295147905179352825856), by norm_num⟩
  | 2 => ⟨((366411133119/9444732965739290427392), (-21147242525/9444732965739290427392)), (1/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-511099786973/151115727451828646838272), (33723316863/151115727451828646838272)), (7/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((305517694175/1208925819614629174706176), (-22687193899/1208925819614629174706176)), (5/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-328707732257/19342813113834066795298816), (27133069405/19342813113834066795298816)), (3/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((163719369357/154742504910672534362390528), (-3718165255/38685626227668133590597632)), (3/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((-38439382721/618970019642690137449562112), (3811363527/618970019642690137449562112)), (3/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((275657359395/79228162514264337593543950336), (-14813318863/39614081257132168796771975168)), (7/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((-29741480949/158456325028528675187087900672), (55112065533/2535301200456458802993406410752)), (13/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((99518290365/10141204801825835211973625643008), (-12357109919/10141204801825835211973625643008)), (11/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((-324327556031/649037107316853453566312041152512), (42986620505/649037107316853453566312041152512)), (5/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((258353880081/10384593717069655257060992658440192), (-284452831/81129638414606681695789005144064)), (1/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359738872393/17179869184), (2418151493/8589934592)), (9/17179869184), by norm_num⟩
  | 1 => ⟨((351235565293/274877906944), (1175285157/274877906944)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((341399551383/35184372088832), (-1459014563/17592186044416)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-282517817485/2251799813685248), (4827447971/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((350486941075/144115188075855872), (-8979906919/144115188075855872)), (15/144115188075855872), by norm_num⟩
  | 5 => ⟨((-521473020051/9223372036854775808), (1113036803/576460752303423488)), (31/9223372036854775808), by norm_num⟩
  | 6 => ⟨((107699363813/73786976294838206464), (-18384920953/295147905179352825856)), (3/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-95273599893/2361183241434822606848), (19512167389/9444732965739290427392)), (27/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((176891712029/151115727451828646838272), (-21129170919/302231454903657293676544)), (31/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-170201819881/4835703278458516698824704), (23231572743/9671406556917033397649408)), (75/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((21043810059/19342813113834066795298816), (-25849439171/309485009821345068724781056)), (97/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-42552483709/1237940039285380274899124224), (29038314847/9903520314283042199192993792)), (59/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((350361661515/316912650057057350374175801344), (-32876117569/316912650057057350374175801344)), (155/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-293128906495/37778931862957161709568), (16917794021/37778931862957161709568)), (1/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((38332484023/18889465931478580854784), (-10116995059/75557863725914323419136)), (5/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-366621233009/1208925819614629174706176), (3403079085/151115727451828646838272)), (3/604462909807314587353088), by norm_num⟩
  | 3 => ⟨((328707732257/9671406556917033397649408), (-27133069405/9671406556917033397649408)), (7/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((-491158108071/154742504910672534362390528), (11154495765/38685626227668133590597632)), (9/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((322890814857/1237940039285380274899124224), (-32015453627/1237940039285380274899124224)), (1/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((-385920303153/19807040628566084398385987584), (2592330801/1237940039285380274899124224)), (9/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((428277325667/316912650057057350374175801344), (-12400214745/79228162514264337593543950336)), (11/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((-223916153321/2535301200456458802993406410752), (13901748659/1267650600228229401496703205376)), (3/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((445950389543/81129638414606681695789005144064), (-14776650799/20282409603651670423947251286016)), (7/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-213141951067/649037107316853453566312041152512), (30038218953/649037107316853453566312041152512)), (13/1298074214633706907132624082305024), by norm_num⟩
  | 11 => ⟨((196782979771/10384593717069655257060992658440192), (-58775101497/20769187434139310514121985316880384)), (13/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((-352647680679/332306998946228968225951765070086144), (27818600525/166153499473114484112975882535043072)), (13/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359738872393/17179869184), (2418151493/8589934592)), (5/8589934592), by norm_num⟩
  | 1 => ⟨((175617782647/137438953472), (1175285157/274877906944)), (3/137438953472), by norm_num⟩
  | 2 => ⟨((85349887843/8796093022208), (-2918029125/35184372088832)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-4414340897/35184372088832), (4827447965/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 4 => ⟨((175243470309/72057594037927936), (-8979906877/144115188075855872)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-521473017645/9223372036854775808), (17808588609/9223372036854775808)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((430797449501/295147905179352825856), (-18384920335/295147905179352825856)), (49/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-47636798351/1180591620717411303424), (19512165911/9444732965739290427392)), (55/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((353783397365/302231454903657293676544), (-21129167605/302231454903657293676544)), (63/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-340403586601/9671406556917033397649408), (23231565697/9671406556917033397649408)), (19/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((168350429655/154742504910672534362390528), (-1615589053/19342813113834066795298816)), (49/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-340419682005/9903520314283042199192993792), (29038286821/9903520314283042199192993792)), (119/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((87590331301/79228162514264337593543950336), (-32876064509/316912650057057350374175801344)), (39/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((148129791115/2417851639229258349412352), (-21999703175/4835703278458516698824704)), (3/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((-398433614857/19342813113834066795298816), (32888568975/19342813113834066795298816)), (9/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((297671580649/77371252455336267181195264), (-13520600927/38685626227668133590597632)), (3/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((-326152338239/618970019642690137449562112), (32338842047/618970019642690137449562112)), (1/77371252455336267181195264), by norm_num⟩
  | 4 => ⟨((292363866025/4951760157141521099596496896), (-3927773941/618970019642690137449562112)), (1/618970019642690137449562112), by norm_num⟩
  | 5 => ⟨((-227116763611/39614081257132168796771975168), (52606971645/79228162514264337593543950336)), (13/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((158324552853/316912650057057350374175801344), (-39318077015/633825300114114700748351602688)), (9/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-405409445039/10141204801825835211973625643008), (3358329727/633825300114114700748351602688)), (3/2535301200456458802993406410752), by norm_num⟩
  | 8 => ⟨((15137922661/5070602400912917605986812821504), (-34134339719/81129638414606681695789005144064)), (9/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((-136654847063/649037107316853453566312041152512), (20408021353/649037107316853453566312041152512)), (5/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((9183533351/649037107316853453566312041152512), (-362221361/162259276829213363391578010288128)), (11/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((-37899437843/41538374868278621028243970633760768), (12599433263/83076749736557242056487941267521536)), (3/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((301816714101/5316911983139663491615228241121378304), (-1647702737/166153499473114484112975882535043072)), (3/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359738872393/17179869184), (2418151493/8589934592)), (11/17179869184), by norm_num⟩
  | 1 => ⟨((175617782647/137438953472), (1175285157/274877906944)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((85349887843/8796093022208), (-2918029125/35184372088832)), (5/35184372088832), by norm_num⟩
  | 3 => ⟨((-282517817409/2251799813685248), (4827447965/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 4 => ⟨((350486940627/144115188075855872), (-4489953439/72057594037927936)), (17/144115188075855872), by norm_num⟩
  | 5 => ⟨((-260736508849/4611686018427387904), (17808588615/9223372036854775808)), (33/9223372036854775808), by norm_num⟩
  | 6 => ⟨((26924840603/18446744073709551616), (-18384920353/295147905179352825856)), (25/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-190547193593/4722366482869645213696), (19512165961/9444732965739290427392)), (7/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((353783398267/302231454903657293676544), (-5282291933/75557863725914323419136)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-340403588637/9671406556917033397649408), (23231566001/9671406556917033397649408)), (77/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((336700863689/309485009821345068724781056), (-25849425539/309485009821345068724781056)), (99/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-340419691041/9903520314283042199192993792), (29038288323/9903520314283042199192993792)), (15/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((175180671597/158456325028528675187087900672), (-8219016913/79228162514264337593543950336)), (157/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-241103076605/309485009821345068724781056), (43804765965/618970019642690137449562112)), (3/154742504910672534362390528), by norm_num⟩
  | 1 => ⟨((198128585251/618970019642690137449562112), (-9822479057/309485009821345068724781056)), (11/1237940039285380274899124224), by norm_num⟩
  | 2 => ⟨((-44400754159/618970019642690137449562112), (38176236213/4951760157141521099596496896)), (11/4951760157141521099596496896), by norm_num⟩
  | 3 => ⟨((229945324037/19807040628566084398385987584), (-1664442189/1237940039285380274899124224)), (13/39614081257132168796771975168), by norm_num⟩
  | 4 => ⟨((-120222270353/79228162514264337593543950336), (59711629051/316912650057057350374175801344)), (17/316912650057057350374175801344), by norm_num⟩
  | 5 => ⟨((430981425417/2535301200456458802993406410752), (-57122605325/2535301200456458802993406410752)), (1/158456325028528675187087900672), by norm_num⟩
  | 6 => ⟨((-85828139969/5070602400912917605986812821504), (24191619227/10141204801825835211973625643008)), (3/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((124521098005/81129638414606681695789005144064), (-37191936937/162259276829213363391578010288128)), (5/81129638414606681695789005144064), by norm_num⟩
  | 8 => ⟨((-41840581619/324518553658426726783156020576256), (52809486161/2596148429267413814265248164610048)), (7/1298074214633706907132624082305024), by norm_num⟩
  | 9 => ⟨((26380368777/2596148429267413814265248164610048), (-70159921049/41538374868278621028243970633760768)), (17/41538374868278621028243970633760768), by norm_num⟩
  | 10 => ⟨((-126049936477/166153499473114484112975882535043072), (1376284451/10384593717069655257060992658440192)), (11/332306998946228968225951765070086144), by norm_num⟩
  | 11 => ⟨((287435669611/5316911983139663491615228241121378304), (-26328619877/2658455991569831745807614120560689152)), (13/5316911983139663491615228241121378304), by norm_num⟩
  | 12 => ⟨((-78674335467/21267647932558653966460912964485513216), (60334359785/85070591730234615865843651857942052864)), (15/85070591730234615865843651857942052864), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359738872393/17179869184), (2418151493/8589934592)), (3/4294967296), by norm_num⟩
  | 1 => ⟨((175617782647/137438953472), (1175285157/274877906944)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((85349887843/8796093022208), (-2918029125/35184372088832)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-282517817409/2251799813685248), (4827447965/2251799813685248)), (11/2251799813685248), by norm_num⟩
  | 4 => ⟨((350486940627/144115188075855872), (-4489953439/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 5 => ⟨((-16296031803/288230376151711744), (17808588615/9223372036854775808)), (17/4611686018427387904), by norm_num⟩
  | 6 => ⟨((430797449643/295147905179352825856), (-574528761/9223372036854775808)), (51/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-95273596793/2361183241434822606848), (19512165959/9444732965739290427392)), (57/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((88445849557/75557863725914323419136), (-10564583863/151115727451828646838272)), (65/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-340403588539/9671406556917033397649408), (23231565985/9671406556917033397649408)), (39/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((168350431727/154742504910672534362390528), (-12924712749/154742504910672534362390528)), (25/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-170209845253/4951760157141521099596496896), (29038288225/9903520314283042199192993792)), (121/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((175180671011/158456325028528675187087900672), (-32876067427/316912650057057350374175801344)), (79/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1250529330604753/1048576), (180820144671389/524288)), (4593/4096), by norm_num⟩
  | 1 => ⟨((194868719333/128), (28530657841/64)), (381/256), by norm_num⟩
  | 2 => ⟨((62931648153/64), (9322101635/32)), 1, by norm_num⟩
  | 3 => ⟨((219200703817/512), (16414734403/128)), (231/512), by norm_num⟩
  | 4 => ⟨((72329308991/512), (21891771237/512)), (79/512), by norm_num⟩
  | 5 => ⟨((308510941337/8192), (94301464541/8192)), (349/8192), by norm_num⟩
  | 6 => ⟨((276715541869/32768), (85379498005/32768)), (325/32768), by norm_num⟩
  | 7 => ⟨((214632477339/131072), (66818862849/131072)), (263/131072), by norm_num⟩
  | 8 => ⟨((146902367257/524288), (92251825265/1048576)), (375/1048576), by norm_num⟩
  | 9 => ⟨((45048239909/1048576), (114088155687/8388608)), (15/262144), by norm_num⟩
  | 10 => ⟨((12529017861/2097152), (127924420895/67108864)), (559/67108864), by norm_num⟩
  | 11 => ⟨((408491837927/536870912), (16415804201/67108864)), (597/536870912), by norm_num⟩
  | 12 => ⟨((24014549313/268435456), (62214871737/2147483648)), (591/4294967296), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1611251879707105/10141204801825835211973625643008), (183349027511/5070602400912917605986812821504)), (911/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((907460392163103/316912650057057350374175801344), (450451001475/633825300114114700748351602688)), (1119/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1930458839557465/39614081257132168796771975168), (508154672839/39614081257132168796771975168)), (1263/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1932821436822523/2475880078570760549798248448), (33818590023/154742504910672534362390528)), (21/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1814535612882971/154742504910672534362390528), (135605146587/38685626227668133590597632)), (337/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((6211876259685/37778931862957161709568), (254964725539/4835703278458516698824704)), (1267/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((323610218428135/151115727451828646838272), (447603580699/604462909807314587353088)), (139/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1945823037797915/75557863725914323419136), (730020550479/75557863725914323419136)), (1813/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((670573563772567/2361183241434822606848), (549858130943/4722366482869645213696)), (683/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1681546370915613/590295810358705651712), (759882732565/590295810358705651712)), (59/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1898804884992299/73786976294838206464), (477815950269/36893488147419103232)), (1187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((953845061848407/4611686018427387904), (1083091510445/9223372036854775808)), (2691/9223372036854775808), by norm_num⟩
  | 6 => ⟨((839649585771997/576460752303423488), (546594808399/576460752303423488)), (2717/1152921504606846976), by norm_num⟩
  | 5 => ⟨((634819281531659/72057594037927936), (968027779639/144115188075855872)), (1203/72057594037927936), by norm_num⟩
  | 4 => ⟨((1605049087524121/36028797018963968), (1475335465233/36028797018963968)), (3667/36028797018963968), by norm_num⟩
  | 3 => ⟨((12753777216369/70368744177664), (1885664280811/9007199254740992)), (293/562949953421312), by norm_num⟩
  | 2 => ⟨((1259427064069871/2251799813685248), (1949395366155/2251799813685248)), (4849/2251799813685248), by norm_num⟩
  | 1 => ⟨((83245354363551/70368744177664), (3088755039007/1125899906842624)), (961/140737488355328), by norm_num⟩
  | 0 => ⟨((1561666558428765/1125899906842624), (3434589120341/562949953421312)), (535/35184372088832), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1561666558428765/1125899906842624), (3434589120341/562949953421312)), (2040863171327103/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2166049787626393/1125899906842624), (4763907465115/281474976710656)), (23851/562949953421312), by norm_num⟩
  | 2 => ⟨((1041701961456579/281474976710656), (2291247359195/35184372088832)), (92579/562949953421312), by norm_num⟩
  | 3 => ⟨((963502156616317/70368744177664), (4239802941185/8796093022208)), (174327/140737488355328), by norm_num⟩
  | 4 => ⟨((823506548596925/4398046511104), (116104367789943/8796093022208)), (308869/8796093022208), by norm_num⟩
  | 5 => ⟨((599336562181069/17179869184), (84921143180349/17179869184)), (241839/17179869184), by norm_num⟩
  | 6 => ⟨((1250529330604753/1048576), (180820144671389/524288)), (4593/4096), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((359738872393/17179869184), (2418151493/8589934592)), (3/4294967296), by norm_num⟩, 0, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/3117481), (-180480/3117481)), 0, by norm_num⟩
  | 1 => ⟨((-2521267404800/9718687785361), (406585344000/9718687785361)), 0, by norm_num⟩
  | 2 => ⟨((406923320731/4398046511104), (-24876763487/1099511627776)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-288296167273/8796093022208), (47732610409/4398046511104)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((202806061233/17592186044416), (-42838391273/8796093022208)), (1/8796093022208), by norm_num⟩
  | 5 => ⟨((-283189247365/70368744177664), (73654047499/35184372088832)), (1/17592186044416), by norm_num⟩
  | 6 => ⟨((196114289543/140737488355328), (-122844588877/140737488355328)), (1/35184372088832), by norm_num⟩
  | 7 => ⟨((-269214330469/562949953421312), (100125388671/281474976710656)), (7/562949953421312), by norm_num⟩
  | 8 => ⟨((182950524281/1125899906842624), (-160293760751/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 9 => ⟨((-245853060955/4503599627370496), (252850743817/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 10 => ⟨((81511847783/4503599627370496), (-98475935557/4503599627370496)), (9/9007199254740992), by norm_num⟩
  | 11 => ⟨((-53202234059/9007199254740992), (151762173313/18014398509481984)), (15/36028797018963968), by norm_num⟩
  | 12 => ⟨((136211222289/72057594037927936), (-231657355695/72057594037927936)), (13/72057594037927936), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (141/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (141/1280)))⁻¹=value ((2252800/3117481), (-180480/3117481)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/3117481), (-180480/3117481))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/9261481), (-180480/9261481)), 0, by norm_num⟩
  | 1 => ⟨((-7554432204800/85775030313361), (702283776000/85775030313361)), 0, by norm_num⟩
  | 2 => ⟨((324083741981/17592186044416), (-45354919863/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-135279552035/35184372088832), (12685643793/17592186044416)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((112686250265/140737488355328), (-13295930511/70368744177664)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((-374614330433/2251799813685248), (106947788637/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 6 => ⟨((155309647095/4503599627370496), (-52234154505/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 7 => ⟨((-128470528325/18014398509481984), (49945322377/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 8 => ⟨((106006887675/72057594037927936), (-93951971347/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 9 => ⟨((-174492945751/576460752303423488), (174421415789/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 10 => ⟨((143227019943/2305843009213693952), (-160167382909/4611686018427387904)), (11/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-234464218139/18446744073709551616), (72876308389/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 12 => ⟨((23917387871/9223372036854775808), (-65806827709/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (141/1280)))⁻¹=value ((3891200/9261481), (-180480/9261481)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/9261481), (-180480/9261481))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8733522329600/28872491049361), (-1108869120000/28872491049361)), 0, by norm_num⟩
  | 1 => ⟨((-376807136143/2199023255552), (36996265443/1099511627776)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((81475596309/1099511627776), (-44084161991/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-254476279265/8796093022208), (89122398921/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((94360139975/8796093022208), (-41176399959/8796093022208)), (1/8796093022208), by norm_num⟩
  | 5 => ⟨((-271482549539/70368744177664), (143965976603/70368744177664)), (5/70368744177664), by norm_num⟩
  | 6 => ⟨((191260863071/140737488355328), (-30303067887/35184372088832)), (5/140737488355328), by norm_num⟩
  | 7 => ⟨((-265199626459/562949953421312), (198689986017/562949953421312)), (1/70368744177664), by norm_num⟩
  | 8 => ⟨((181294166661/1125899906842624), (-79779880487/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 9 => ⟨((-244489834817/4503599627370496), (252169410161/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 10 => ⟨((162464215019/9007199254740992), (-98319522097/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 11 => ⟨((-106175499155/18014398509481984), (151619836773/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 12 => ⟨((136024367697/72057594037927936), (-231528826735/72057594037927936)), (7/36028797018963968), by norm_num⟩
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
  | 0 => ⟨((27/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/2075809), (-60160/6227427)), 0, by norm_num⟩
  | 1 => ⟨((-1696883507200/38780847040329), (12320768000/4308983004481)), 0, by norm_num⟩
  | 2 => ⟨((227347970863/35184372088832), (-44649195101/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-268300042445/281474976710656), (8803949389/70368744177664)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((158143019855/1125899906842624), (-52060466455/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((-372446900289/18014398509481984), (18464386643/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((219047403241/72057594037927936), (-101833797723/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((-128683969485/288230376151711744), (34373078885/288230376151711744)), (5/576460752303423488), by norm_num⟩
  | 8 => ⟨((302047581615/4611686018427387904), (-91335425183/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-354071987197/36893488147419103232), (59902954529/18446744073709551616)), (9/36893488147419103232), by norm_num⟩
  | 10 => ⟨((51820596477/36893488147419103232), (-77761561019/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-121200861349/590295810358705651712), (50036786495/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 12 => ⟨((283118166861/9444732965739290427392), (-127846378527/9444732965739290427392)), (13/9444732965739290427392), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (141/1280)))⁻¹=value ((614400/2075809), (-60160/6227427)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/2075809), (-60160/6227427))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((196062860983/2199023255552), (-62846011733/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-279353206821/4398046511104), (62275724245/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((273299946099/8796093022208), (-39810084355/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-229040767583/17592186044416), (41940035349/8796093022208)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((354210966705/70368744177664), (-158871079369/70368744177664)), (5/70368744177664), by norm_num⟩
  | 5 => ⟨((-261230722417/140737488355328), (140912364249/140737488355328)), (5/140737488355328), by norm_num⟩
  | 6 => ⟨((186835263559/281474976710656), (-14959925161/35184372088832)), (5/281474976710656), by norm_num⟩
  | 7 => ⟨((-261436258327/1125899906842624), (49299082403/281474976710656)), (9/1125899906842624), by norm_num⟩
  | 8 => ⟨((89855775563/1125899906842624), (-79424029943/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 9 => ⟨((-60792457589/2251799813685248), (125751350625/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 10 => ⟨((161917385985/18014398509481984), (-196330963463/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 11 => ⟨((-211900457897/72057594037927936), (302958054469/72057594037927936)), (17/72057594037927936), by norm_num⟩
  | 12 => ⟨((33959918281/36028797018963968), (-231401273165/144115188075855872)), (7/72057594037927936), by norm_num⟩
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
  | 0 => ⟨((35/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/31379881), (-180480/31379881)), 0, by norm_num⟩
  | 1 => ⟨((-25673825484800/984696931574161), (1293680640000/984696931574161)), 0, by norm_num⟩
  | 2 => ⟨((418565235787/140737488355328), (-7917543937/35184372088832)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-381717161617/1125899906842624), (38566682075/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((21743136149/562949953421312), (-22010172087/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((-316856779277/72057594037927936), (24112586433/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((288404626475/576460752303423488), (-12838300777/144115188075855872)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-262335747733/4611686018427387904), (53556739347/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 8 => ⟨((119232875321/18446744073709551616), (-54970388625/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-108311528961/147573952589676412928), (111425800331/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 10 => ⟨((393296332759/4722366482869645213696), (-27944414313/1180591620717411303424)), (3/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-356785863099/37778931862957161709568), (111180073541/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((40429969875/37778931862957161709568), (-109794104027/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (141/1280)))⁻¹=value ((7168000/31379881), (-180480/31379881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/31379881), (-180480/31379881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((178420990625/8796093022208), (-66443982041/17592186044416)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-73594788417/4398046511104), (71943449519/17592186044416)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((314714452935/35184372088832), (-48581930093/17592186044416)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-34834577817/8796093022208), (105915911927/70368744177664)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((223042931247/140737488355328), (-51226016407/70368744177664)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((-336165780735/562949953421312), (92066775361/281474976710656)), (7/562949953421312), by norm_num⟩
  | 6 => ⟨((243689439627/1125899906842624), (-78822293795/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 7 => ⟨((-85964067555/1125899906842624), (130508846959/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 8 => ⟨((7424808345/281474976710656), (-210875973229/9007199254740992)), (3/2251799813685248), by norm_num⟩
  | 9 => ⟨((-10078739257/1125899906842624), (83616588991/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 10 => ⟨((215176611081/72057594037927936), (-130684943815/36028797018963968)), (15/72057594037927936), by norm_num⟩
  | 11 => ⟨((-70485658247/72057594037927936), (201786255577/144115188075855872)), (13/144115188075855872), by norm_num⟩
  | 12 => ⟨((180876081943/576460752303423488), (-154183112539/288230376151711744)), (19/576460752303423488), by norm_num⟩
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
  | 0 => ⟨((43/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/47354281), (-180480/47354281)), 0, by norm_num⟩
  | 1 => ⟨((-38760053964800/2242427929026961), (1589379072000/2242427929026961)), 0, by norm_num⟩
  | 2 => ⟨((452011737235/281474976710656), (-27822003787/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-167907727183/1125899906842624), (27587011403/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((249383688331/18014398509481984), (-25640784657/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-185119048823/144115188075855872), (45750756781/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((137356438229/1152921504606846976), (-39677091613/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((-407493557551/36893488147419103232), (33702762335/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((302096101185/295147905179352825856), (-56353464619/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-447724408643/4722366482869645213696), (23262667853/1180591620717411303424)), (5/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((82907951809/9444732965739290427392), (-9505441905/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-245532859849/302231454903657293676544), (61622533963/302231454903657293676544)), (7/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((90852987169/1208925819614629174706176), (-24791272985/1208925819614629174706176)), (3/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (141/1280)))⁻¹=value ((8806400/47354281), (-180480/47354281)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/47354281), (-180480/47354281))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((264432389021/70368744177664), (-54866010887/70368744177664)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-60591894991/17592186044416), (1987820391/2199023255552)), (3/70368744177664), by norm_num⟩
  | 2 => ⟨((69364195273/35184372088832), (-89828705451/140737488355328)), (3/140737488355328), by norm_num⟩
  | 3 => ⟨((-128470660677/140737488355328), (12599908037/35184372088832)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((211752654603/562949953421312), (-99336423053/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-162629565769/1125899906842624), (90328965135/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 6 => ⟨((238670223217/4503599627370496), (-38954758019/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 7 => ⟨((-169694435951/9007199254740992), (64795099779/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 8 => ⟨((117826392753/18014398509481984), (-52495019497/9007199254740992)), (13/36028797018963968), by norm_num⟩
  | 9 => ⟨((-160431127887/72057594037927936), (41701640993/18014398509481984)), (5/36028797018963968), by norm_num⟩
  | 10 => ⟨((26809793485/36028797018963968), (-65242735301/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 11 => ⟨((-17585019821/72057594037927936), (6300074199/18014398509481984)), (7/288230376151711744), by norm_num⟩
  | 12 => ⟨((180635281331/2305843009213693952), (-308198651955/2305843009213693952)), (5/576460752303423488), by norm_num⟩
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
  | 0 => ⟨((51/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/22201827), (-60160/22201827)), 0, by norm_num⟩
  | 1 => ⟨((-673217740800/54769013570881), (209453056000/492921122137929)), 0, by norm_num⟩
  | 2 => ⟨((271119710509/281474976710656), (-14065567581/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-84955548889/1125899906842624), (23522835981/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((26612895917/4503599627370496), (-36876535985/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((-266693158611/576460752303423488), (3468314945/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((333972396201/9223372036854775808), (-40590008353/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-418097627627/147573952589676412928), (7270120267/18446744073709551616)), (1/18446744073709551616), by norm_num⟩
  | 8 => ⟨((65406767509/295147905179352825856), (-41013914585/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-40916155681/2361183241434822606848), (57124498647/18889465931478580854784)), (9/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((102351296685/75557863725914323419136), (-78759926161/302231454903657293676544)), (3/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-127975675245/1208925819614629174706176), (26920340831/1208925819614629174706176)), (9/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((159965423829/19342813113834066795298816), (-73092993841/38685626227668133590597632)), (13/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (141/1280)))⁻¹=value ((3481600/22201827), (-60160/22201827)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/22201827), (-60160/22201827))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((330548316191/562949953421312), (-37281572553/281474976710656)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-328494454007/562949953421312), (91348911349/562949953421312)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((99348875811/281474976710656), (-133922220135/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 3 => ⟨((-382109904235/2251799813685248), (154103235865/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((322999485419/4503599627370496), (-154411769781/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 5 => ⟨((-63074548341/2251799813685248), (141935013917/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((93600028599/9007199254740992), (-123267827219/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 7 => ⟨((-16757561967/4503599627370496), (102964114029/36028797018963968)), (13/72057594037927936), by norm_num⟩
  | 8 => ⟨((187028155287/144115188075855872), (-83643204725/72057594037927936)), (11/144115188075855872), by norm_num⟩
  | 9 => ⟨((-255400693187/576460752303423488), (133110534375/288230376151711744)), (17/576460752303423488), by norm_num⟩
  | 10 => ⟨((21379425275/144115188075855872), (-52115507925/288230376151711744)), (7/576460752303423488), by norm_num⟩
  | 11 => ⟨((-3509832695/72057594037927936), (322272530015/4611686018427387904)), (23/4611686018427387904), by norm_num⟩
  | 12 => ⟨((144317658525/9223372036854775808), (-246425824299/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
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
  | 0 => ⟨((59/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/89133481), (-180480/89133481)), 0, by norm_num⟩
  | 1 => ⟨((-72985574604800/7944777435177361), (2180775936000/7944777435177361)), 0, by norm_num⟩
  | 2 => ⟨((175191214053/281474976710656), (-490929559/17592186044416)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-47467075367/1125899906842624), (2839124191/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((102864468617/36028797018963968), (-30783539621/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((-445728982629/2305843009213693952), (40049918673/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((482746027485/36893488147419103232), (-12663621745/9223372036854775808)), (3/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-65339921791/73786976294838206464), (245135965/2305843009213693952)), (1/73786976294838206464), by norm_num⟩
  | 8 => ⟨((70734326603/1180591620717411303424), (-19131290903/2361183241434822606848)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-306226786325/75557863725914323419136), (1439972241/2361183241434822606848)), (3/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((331357699039/1208925819614629174706176), (-27466712897/604462909807314587353088)), (7/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-358468841969/19342813113834066795298816), (32471524727/9671406556917033397649408)), (9/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((387708837689/309485009821345068724781056), (-76237687767/309485009821345068724781056)), (11/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (141/1280)))⁻¹=value ((12083200/89133481), (-180480/89133481)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/89133481), (-180480/89133481))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((178636544343/2251799813685248), (-86218444003/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((-378902973859/4503599627370496), (110595124543/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 2 => ⟨((59993607657/1125899906842624), (-83718118805/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-119156913469/4503599627370496), (98492585731/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((206003558593/18014398509481984), (-100180643303/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((-81691603583/18014398509481984), (46502941043/18014398509481984)), (5/36028797018963968), by norm_num⟩
  | 6 => ⟨((244943192153/144115188075855872), (-162594766839/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((-176597243253/288230376151711744), (68187184349/144115188075855872)), (9/288230376151711744), by norm_num⟩
  | 8 => ⟨((123725381967/576460752303423488), (-222142137113/1152921504606846976)), (1/72057594037927936), by norm_num⟩
  | 9 => ⟨((-169430667333/2305843009213693952), (177042746991/2305843009213693952)), (13/2305843009213693952), by norm_num⟩
  | 10 => ⟨((227331835993/9223372036854775808), (-69383856615/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-74725647311/9223372036854775808), (107328036657/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 12 => ⟨((24021516533/9223372036854775808), (-328391552877/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
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
  | 0 => ⟨((67/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/114938281), (-180480/114938281)), 0, by norm_num⟩
  | 1 => ⟨((-94124866764800/13210808439234961), (2476474368000/13210808439234961)), 0, by norm_num⟩
  | 2 => ⟨((478668121777/1125899906842624), (-9448231053/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-57114844673/2251799813685248), (24060197459/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((436081972507/288230376151711744), (-7179663715/72057594037927936)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-52015387729/576460752303423488), (32906005889/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((99252152173/18446744073709551616), (-36654450945/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-378706059105/1180591620717411303424), (1249822563/36893488147419103232)), (3/590295810358705651712), by norm_num⟩
  | 8 => ⟨((361184095689/18889465931478580854784), (-21477090249/9444732965739290427392)), (7/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-344412411521/302231454903657293676544), (45560910291/302231454903657293676544)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((328361723999/4835703278458516698824704), (-47839806387/4835703278458516698824704)), (9/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-156501874385/38685626227668133590597632), (12453664785/19342813113834066795298816)), (5/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((74577793441/309485009821345068724781056), (-25753917215/618970019642690137449562112)), (11/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (141/1280)))⁻¹=value ((13721600/114938281), (-180480/114938281)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/114938281), (-180480/114938281))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((340133690285/36028797018963968), (-86831690011/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 1 => ⟨((-95180021517/9007199254740992), (14479336393/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((250772682547/36028797018963968), (-90183459621/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 3 => ⟨((-256162650081/72057594037927936), (27054986937/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((56474597223/36028797018963968), (-13948495725/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((-90832637595/144115188075855872), (104554816473/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((17183719881/72057594037927936), (-11493687119/72057594037927936)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((-99740882225/1152921504606846976), (154849923177/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 8 => ⟨((70170591915/2305843009213693952), (-252866371381/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-48175923243/4611686018427387904), (100921544089/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 10 => ⟨((129502911749/36893488147419103232), (-39589562661/9223372036854775808)), (13/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-10653854395/9223372036854775808), (122551791413/73786976294838206464)), (19/147573952589676412928), by norm_num⟩
  | 12 => ⟨((109670464371/295147905179352825856), (-93776160085/147573952589676412928)), (15/295147905179352825856), by norm_num⟩
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
  | 0 => ⟨((75/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/48006627), (-60160/48006627)), 0, by norm_num⟩
  | 1 => ⟨((-4368463462400/768212078639043), (308019200000/2304636235917129)), 0, by norm_num⟩
  | 2 => ⟨((85330872801/281474976710656), (-6018042277/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-145550920219/9007199254740992), (6845619389/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((496470708719/576460752303423488), (-29199911675/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((-211651892307/4611686018427387904), (3736384679/1152921504606846976)), (5/9223372036854775808), by norm_num⟩
  | 6 => ⟨((360869699095/147573952589676412928), (-14873635853/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-307601409031/2361183241434822606848), (28998655079/2361183241434822606848)), (3/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((262159581451/37778931862957161709568), (-27825894083/37778931862957161709568)), (3/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-13962479089/37778931862957161709568), (52739418039/1208925819614629174706176)), (11/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((11896481347/604462909807314587353088), (-12369345095/4835703278458516698824704)), (5/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-162156191035/154742504910672534362390528), (23015684207/154742504910672534362390528)), (5/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((138123442755/2475880078570760549798248448), (-42526001951/4951760157141521099596496896)), (5/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (141/1280)))⁻¹=value ((5120000/48006627), (-60160/48006627)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/48006627), (-60160/48006627))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((289336836731/288230376151711744), (-19374020827/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 1 => ⟨((-169527813577/144115188075855872), (26740657793/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((231072484039/288230376151711744), (-10672040945/36028797018963968)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-242014356253/576460752303423488), (13037270713/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((217301912905/1152921504606846976), (-6806260373/72057594037927936)), (9/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-88495322633/1152921504606846976), (51457883921/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((270233881163/9223372036854775808), (-182057753375/9223372036854775808)), (13/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-98620673537/9223372036854775808), (19234460079/2305843009213693952)), (3/4611686018427387904), by norm_num⟩
  | 8 => ⟨((278634183657/73786976294838206464), (-251880067105/73786976294838206464)), (5/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-23974435181/18446744073709551616), (100680119655/73786976294838206464)), (17/147573952589676412928), by norm_num⟩
  | 10 => ⟨((32277333499/73786976294838206464), (-39531958521/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-170126516139/1180591620717411303424), (244887981847/1180591620717411303424)), (5/295147905179352825856), by norm_num⟩
  | 12 => ⟨((13691214813/295147905179352825856), (-46863251367/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
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
  | 0 => ⟨((83/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/176378281), (-180480/176378281)), 0, by norm_num⟩
  | 1 => ⟨((-144456514764800/31109298008514961), (3067871232000/31109298008514961)), 0, by norm_num⟩
  | 2 => ⟨((503746109423/2251799813685248), (-16050352591/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-194127781499/18014398509481984), (8249233619/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((299208981119/576460752303423488), (-7949276011/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((-461118413915/18446744073709551616), (7353539943/4611686018427387904)), (5/18446744073709551616), by norm_num⟩
  | 6 => ⟨((355280322957/295147905179352825856), (-3306622003/36893488147419103232)), (5/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-136851834011/2361183241434822606848), (5825878985/1180591620717411303424)), (5/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((13177128685/4722366482869645213696), (-20207500417/75557863725914323419136)), (9/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-162387096545/1208925819614629174706176), (17305827175/1208925819614629174706176)), (1/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((3908073957/604462909807314587353088), (-29344111441/38685626227668133590597632)), (7/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-385198288963/1237940039285380274899124224), (24671700341/618970019642690137449562112)), (3/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((296582960717/19807040628566084398385987584), (-20598442035/9903520314283042199192993792)), (11/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (141/1280)))⁻¹=value ((16998400/176378281), (-180480/176378281)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/176378281), (-180480/176378281))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((222443569109/2305843009213693952), (-15529450985/576460752303423488)), (7/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-135611298217/1152921504606846976), (5521908527/144115188075855872)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((380963375915/4611686018427387904), (-18028159931/576460752303423488)), (11/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-204022477339/4611686018427387904), (44769750187/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((186218732139/9223372036854775808), (-94578697381/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-306933701285/36893488147419103232), (45051092669/9223372036854775808)), (15/36893488147419103232), by norm_num⟩
  | 6 => ⟨((59063883723/18446744073709551616), (-160259414115/73786976294838206464)), (3/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-173418002159/147573952589676412928), (67969539083/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 8 => ⟨((245912343991/590295810358705651712), (-111518432521/295147905179352825856)), (19/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-84848488861/590295810358705651712), (178565008407/1180591620717411303424)), (1/73786976294838206464), by norm_num⟩
  | 10 => ⟨((228840593195/4722366482869645213696), (-280711670723/4722366482869645213696)), (13/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-150929640871/9444732965739290427392), (217488324699/9444732965739290427392)), (19/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((194471763825/37778931862957161709568), (-333074411289/37778931862957161709568)), (15/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((91/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/212013481), (-180480/212013481)), 0, by norm_num⟩
  | 1 => ⟨((-173648870604800/44949716125737361), (3363569664000/44949716125737361)), 0, by norm_num⟩
  | 2 => ⟨((382270855357/2251799813685248), (-2777146665/562949953421312)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-268748970709/36028797018963968), (1301901891/4503599627370496)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((377843224359/1152921504606846976), (-18309031625/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((-132793144219/9223372036854775808), (15448636711/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((373326476945/590295810358705651712), (-6336317189/147573952589676412928)), (7/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-2049703555/73786976294838206464), (2545746925/1180591620717411303424)), (3/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((46090592665/37778931862957161709568), (-32217401423/302231454903657293676544)), (9/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-64769793223/1208925819614629174706176), (12583666001/2417851639229258349412352)), (7/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((364042098193/154742504910672534362390528), (-38925610937/154742504910672534362390528)), (11/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-127870255219/1237940039285380274899124224), (29852861811/2475880078570760549798248448)), (9/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((89820644951/19807040628566084398385987584), (-45470154783/79228162514264337593543950336)), (13/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (141/1280)))⁻¹=value ((18636800/212013481), (-180480/212013481)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/212013481), (-180480/212013481))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((312012256429/36893488147419103232), (-45198020359/18446744073709551616)), (11/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-98483961685/9223372036854775808), (132061635067/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 2 => ⟨((284180996391/36893488147419103232), (-54995049055/18446744073709551616)), (9/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-77654295067/18446744073709551616), (34655791821/18446744073709551616)), (13/73786976294838206464), by norm_num⟩
  | 4 => ⟨((71951932643/36893488147419103232), (-578154583/576460752303423488)), (15/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-7493481697/9223372036854775808), (71035475237/147573952589676412928)), (13/295147905179352825856), by norm_num⟩
  | 6 => ⟨((93004208383/295147905179352825856), (-127000989279/590295810358705651712)), (11/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-274539704629/2361183241434822606848), (216199515917/2361183241434822606848)), (5/590295810358705651712), by norm_num⟩
  | 8 => ⟨((195363264241/4722366482869645213696), (-22219944185/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-135141943225/9444732965739290427392), (71260059359/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((91266203191/18889465931478580854784), (-224249730867/37778931862957161709568)), (21/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-30127911141/18889465931478580854784), (43460031633/18889465931478580854784)), (17/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((155381149037/302231454903657293676544), (-266320153677/302231454903657293676544)), (25/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((99/8), (141/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/27880609), (-60160/83641827)), 0, by norm_num⟩
  | 1 => ⟨((-22836175667200/6995955223897929), (135528448000/2331985074632643)), 0, by norm_num⟩
  | 2 => ⟨((37113994279/281474976710656), (-7930574541/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-191882240747/36028797018963968), (1708719685/9007199254740992)), (1/36028797018963968), by norm_num⟩
  | 4 => ⟨((495983713817/2305843009213693952), (-22089036417/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((-80120857595/9223372036854775808), (17132569229/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((207066210595/590295810358705651712), (-25837606641/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-133776043173/9444732965739290427392), (19084718193/18889465931478580854784)), (5/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((86419723171/151115727451828646838272), (-6938064275/151115727451828646838272)), (7/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-446583578817/19342813113834066795298816), (39856976643/19342813113834066795298816)), (5/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((288448282065/309485009821345068724781056), (-7083438267/77371252455336267181195264)), (1/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-372587616657/9903520314283042199192993792), (39950133635/9903520314283042199192993792)), (11/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((120307881289/79228162514264337593543950336), (-27968193873/158456325028528675187087900672)), (1/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (141/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (141/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (141/1280)))⁻¹=value ((2252800/27880609), (-60160/83641827)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/27880609), (-60160/83641827))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((402337535365/590295810358705651712), (-30114275669/147573952589676412928)), (15/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-130995628623/147573952589676412928), (90138774193/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 2 => ⟨((387235544623/590295810358705651712), (-152940344195/590295810358705651712)), (13/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-6736847163/18446744073709551616), (97713365383/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 4 => ⟨((202540009811/1180591620717411303424), (-52690303003/590295810358705651712)), (11/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-340953364241/4722366482869645213696), (203753904131/4722366482869645213696)), (5/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((266418186343/9444732965739290427392), (-91519893371/4722366482869645213696)), (17/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-197617510341/18889465931478580854784), (39078883191/4722366482869645213696)), (15/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((2204968649/590295810358705651712), (-128802989057/37778931862957161709568)), (3/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-97847425663/75557863725914323419136), (103413530851/75557863725914323419136)), (21/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((132364762657/302231454903657293676544), (-2544704185/4722366482869645213696)), (1/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-87478214733/604462909807314587353088), (252641349849/1208925819614629174706176)), (13/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((440871477/9444732965739290427392), (-193586679185/2417851639229258349412352)), (19/2417851639229258349412352), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((485564504375/549755813888), (-569952671/68719476736)), (569/549755813888), by norm_num⟩
  | 1 => ⟨((-155370990997/4398046511104), (225433303131/4398046511104)), (12131/4398046511104), by norm_num⟩
  | 2 => ⟨((125155451273/1099511627776), (-34321638331/2199023255552)), (4201/1099511627776), by norm_num⟩
  | 3 => ⟨((-97918026293/4398046511104), (24658532555/2199023255552)), (32339/8796093022208), by norm_num⟩
  | 4 => ⟨((52528895119/4398046511104), (-19836179817/4398046511104)), (6095/2199023255552), by norm_num⟩
  | 5 => ⟨((-260664200165/70368744177664), (73024216701/35184372088832)), (30771/17592186044416), by norm_num⟩
  | 6 => ⟨((24296881243/17592186044416), (-120738449155/140737488355328)), (2121/2199023255552), by norm_num⟩
  | 7 => ⟨((-263983681269/562949953421312), (198973721235/562949953421312)), (269833/562949953421312), by norm_num⟩
  | 8 => ⟨((181611247009/1125899906842624), (-159515514819/1125899906842624)), (247409/1125899906842624), by norm_num⟩
  | 9 => ⟨((-244401247289/4503599627370496), (252198863345/4503599627370496)), (426279/4503599627370496), by norm_num⟩
  | 10 => ⟨((162490346519/9007199254740992), (-49159300323/2251799813685248)), (175011/4503599627370496), by norm_num⟩
  | 11 => ⟨((-212347847327/36028797018963968), (151621325229/18014398509481984)), (277005/18014398509481984), by norm_num⟩
  | 12 => ⟨((34006631819/18014398509481984), (-115764534041/36028797018963968)), (213083/36028797018963968), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((485564504375/549755813888), (-569952671/68719476736)), (285/274877906944), by norm_num⟩
  | 1 => ⟨((-155370990997/4398046511104), (225433303131/4398046511104)), (3033/1099511627776), by norm_num⟩
  | 2 => ⟨((125155451273/1099511627776), (-34321638331/2199023255552)), (8403/2199023255552), by norm_num⟩
  | 3 => ⟨((-97918026293/4398046511104), (24658532555/2199023255552)), (8085/2199023255552), by norm_num⟩
  | 4 => ⟨((52528895119/4398046511104), (-19836179817/4398046511104)), (48761/17592186044416), by norm_num⟩
  | 5 => ⟨((-260664200165/70368744177664), (73024216701/35184372088832)), (123087/70368744177664), by norm_num⟩
  | 6 => ⟨((24296881243/17592186044416), (-120738449155/140737488355328)), (67875/70368744177664), by norm_num⟩
  | 7 => ⟨((-263983681269/562949953421312), (198973721235/562949953421312)), (8433/17592186044416), by norm_num⟩
  | 8 => ⟨((181611247009/1125899906842624), (-159515514819/1125899906842624)), (247455/1125899906842624), by norm_num⟩
  | 9 => ⟨((-244401247289/4503599627370496), (252198863345/4503599627370496)), (106615/1125899906842624), by norm_num⟩
  | 10 => ⟨((162490346519/9007199254740992), (-49159300323/2251799813685248)), (350383/9007199254740992), by norm_num⟩
  | 11 => ⟨((-212347847327/36028797018963968), (151621325229/18014398509481984)), (138863/9007199254740992), by norm_num⟩
  | 12 => ⟨((34006631819/18014398509481984), (-115764534041/36028797018963968)), (429049/72057594037927936), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile000Gamma
