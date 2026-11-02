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
namespace Reinmann.XiRectangle.Tile001Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/640))
  have he : value ((3/4), (423/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/293273329), (-541440/293273329)), 0, by norm_num⟩
  | 1 => ⟨((-239956353843200/86009245502742241), (11864899584000/86009245502742241)), 0, by norm_num⟩
  | 2 => ⟨((117210672617/1125899906842624), (-17404547917/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-279744064827/72057594037927936), (27732294437/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 4 => ⟨((333623746085/2305843009213693952), (-20709119003/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-49704293645/9223372036854775808), (29685889137/36893488147419103232)), (5/73786976294838206464), by norm_num⟩
  | 6 => ⟨((236815365317/1180591620717411303424), (-41363312445/1180591620717411303424)), (1/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-140949235449/18889465931478580854784), (14111619335/9444732965739290427392)), (3/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((5239862735/18889465931478580854784), (-18952649239/302231454903657293676544)), (1/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-199341836401/19342813113834066795298816), (50269983039/19342813113834066795298816)), (5/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((14802161183/38685626227668133590597632), (-16496937493/154742504910672534362390528)), (7/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-70298514209/4951760157141521099596496896), (85886343777/19807040628566084398385987584)), (5/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((333639437463/633825300114114700748351602688), (-13873260825/79228162514264337593543950336)), (13/633825300114114700748351602688), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (423/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (423/1280)))⁻¹=value ((21913600/293273329), (-541440/293273329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/293273329), (-541440/293273329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((356474374705/137438953472), (424392897/17179869184)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((10956800/293273329), (-270720/293273329)), 0, by norm_num⟩
  | 2 => ⟨((-59989088460800/86009245502742241), (2966224896000/86009245502742241)), 0, by norm_num⟩
  | 3 => ⟨((312561793645/18014398509481984), (-23206063889/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-279744064827/576460752303423488), (27732294437/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((66724749217/4611686018427387904), (-33134590405/18446744073709551616)), (3/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-265089566107/590295810358705651712), (9895296379/147573952589676412928)), (1/147573952589676412928), by norm_num⟩
  | 7 => ⟨((270646131791/18889465931478580854784), (-5909044635/2361183241434822606848)), (5/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-140949235449/302231454903657293676544), (14111619335/151115727451828646838272)), (3/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((74522492231/4835703278458516698824704), (-33693598647/9671406556917033397649408)), (1/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-159473469121/309485009821345068724781056), (40215986431/309485009821345068724781056)), (9/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((344486660259/19807040628566084398385987584), (-95982181777/19807040628566084398385987584)), (11/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-374925409115/633825300114114700748351602688), (28628781259/158456325028528675187087900672)), (7/316912650057057350374175801344), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (9/20480)), 0, by norm_num⟩
  | 45 => ⟨((107534668577/4080638361600), (-17883/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-51783513563911/1915179604377600), (126762470177/197568495616000)), 0, by norm_num⟩
  | 43 => ⟨((486926373233/17592186044416), (-5838187235/8796093022208)), (1/17592186044416), by norm_num⟩
  | 42 => ⟨((-249253381645/8796093022208), (374149283/549755813888)), (1/17592186044416), by norm_num⟩
  | 41 => ⟨((510616684961/17592186044416), (-12260590419/17592186044416)), (1/17592186044416), by norm_num⟩
  | 40 => ⟨((-65415558389/2199023255552), (3139482929/4398046511104)), (1/17592186044416), by norm_num⟩
  | 39 => ⟨((268340119291/8796093022208), (-6434592289/8796093022208)), (1/17592186044416), by norm_num⟩
  | 38 => ⟨((-275367781005/8796093022208), (6598051785/8796093022208)), (1/8796093022208), by norm_num⟩
  | 37 => ⟨((141386746147/4398046511104), (-3385010385/4398046511104)), (1/8796093022208), by norm_num⟩
  | 36 => ⟨((-9080894167/274877906944), (6951194191/8796093022208)), (1/8796093022208), by norm_num⟩
  | 35 => ⟨((18678004115/549755813888), (-7142333785/8796093022208)), (1/8796093022208), by norm_num⟩
  | 34 => ⟨((-76897714805/2199023255552), (7344285809/8796093022208)), (1/8796093022208), by norm_num⟩
  | 33 => ⟨((158430353841/4398046511104), (-7557994813/8796093022208)), (1/8796093022208), by norm_num⟩
  | 32 => ⟨((-326706761729/8796093022208), (973064831/1099511627776)), (1/4398046511104), by norm_num⟩
  | 31 => ⟨((337184480537/8796093022208), (-8025046039/8796093022208)), (1/4398046511104), by norm_num⟩
  | 30 => ⟨((-348356677895/8796093022208), (4140458739/4398046511104)), (1/8796093022208), by norm_num⟩
  | 29 => ⟨((360294783429/8796093022208), (-8553650267/8796093022208)), (1/8796093022208), by norm_num⟩
  | 28 => ⟨((-373080372639/8796093022208), (4422484333/4398046511104)), (1/8796093022208), by norm_num⟩
  | 27 => ⟨((6043859923/137438953472), (-4578420223/4398046511104)), (1/8796093022208), by norm_num⟩
  | 26 => ⟨((-401582671175/8796093022208), (9491521471/8796093022208)), (1/8796093022208), by norm_num⟩
  | 25 => ⟨((52191542147/1099511627776), (-2462902613/2199023255552)), (1/8796093022208), by norm_num⟩
  | 24 => ⟨((-217400898453/4398046511104), (10240116687/8796093022208)), (1/8796093022208), by norm_num⟩
  | 23 => ⟨((453561994447/8796093022208), (-10660544539/8796093022208)), (1/8796093022208), by norm_num⟩
  | 22 => ⟨((-474014738763/8796093022208), (11116999673/8796093022208)), (1/8796093022208), by norm_num⟩
  | 21 => ⟨((496400001753/8796093022208), (-1451790487/1099511627776)), (1/8796093022208), by norm_num⟩
  | 20 => ⟨((-32562836919/549755813888), (12158268019/8796093022208)), (1/8796093022208), by norm_num⟩
  | 19 => ⟨((274089295381/4398046511104), (-3188928965/2199023255552)), (1/4398046511104), by norm_num⟩
  | 18 => ⟨((-36146495267/549755813888), (3353744497/2199023255552)), (1/4398046511104), by norm_num⟩
  | 17 => ⟨((306012354869/4398046511104), (-7073090967/4398046511104)), (1/4398046511104), by norm_num⟩
  | 16 => ⟨((-162468484597/2199023255552), (1870224753/1099511627776)), (1/4398046511104), by norm_num⟩
  | 15 => ⟨((86589639885/1099511627776), (-3969339811/2199023255552)), (1/2199023255552), by norm_num⟩
  | 14 => ⟨((-370806662693/4398046511104), (8456232139/4398046511104)), (1/2199023255552), by norm_num⟩
  | 13 => ⟨((199486040327/2199023255552), (-1130762685/549755813888)), (1/4398046511104), by norm_num⟩
  | 12 => ⟨((-215886696021/2199023255552), (9724613823/4398046511104)), (1/4398046511104), by norm_num⟩
  | 11 => ⟨((470459377171/4398046511104), (-10513420277/4398046511104)), (1/4398046511104), by norm_num⟩
  | 10 => ⟨((-258386122687/2199023255552), (5720932829/2199023255552)), (1/4398046511104), by norm_num⟩
  | 9 => ⟨((71652307173/549755813888), (-6275374229/2199023255552)), (1/2199023255552), by norm_num⟩
  | 8 => ⟨((-80442530021/549755813888), (6949265681/2199023255552)), (1/2199023255552), by norm_num⟩
  | 7 => ⟨((183396528747/1099511627776), (-7786049487/2199023255552)), (1/1099511627776), by norm_num⟩
  | 6 => ⟨((-426520046543/2199023255552), (8853251445/2199023255552)), (1/2199023255552), by norm_num⟩
  | 5 => ⟨((509597738563/2199023255552), (-5130979115/1099511627776)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((-158287434835/549755813888), (6104492751/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((418315856475/1099511627776), (-7540149683/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-77278752825/137438953472), (4938537847/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((300183996701/274877906944), (-3597391039/274877906944)), (1/274877906944), by norm_num⟩
  | 0 => ⟨((-196698541505/1099511627776), (54322290819/2199023255552)), (3/2199023255552), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (423/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (423/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (423/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((356474374705/137438953472), (424392897/17179869184)), (1/137438953472), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (423/1280))) (z:=((-21/128), (423/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((356474374705/137438953472), (424392897/17179869184))) (r:=(1/137438953472)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((71695087275/2147483648), (5047378419/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((244389279031/137438953472), (880503197/68719476736)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((833328847027200/86009245502742241), (-21331851354720/86009245502742241)), 0, by norm_num⟩
  | 3 => ⟨((-70324135353/562949953421312), (14393453949/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((347529801749/144115188075855872), (-26672600693/144115188075855872)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-257157626471/4611686018427387904), (13163829675/2305843009213693952)), (19/4611686018427387904), by norm_num⟩
  | 6 => ⟨((52767215085/36893488147419103232), (-54074750255/295147905179352825856)), (13/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-370621037075/9444732965739290427392), (28526864929/4722366482869645213696)), (33/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((170560374759/151115727451828646838272), (-1918249263/9444732965739290427392)), (5/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-40637363851/1208925819614629174706176), (67021445849/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((318208709693/309485009821345068724781056), (-74017751051/309485009821345068724781056)), (125/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-159041537351/4951760157141521099596496896), (41245762855/4951760157141521099596496896)), (73/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((323389125781/316912650057057350374175801344), (-92616902443/316912650057057350374175801344)), (91/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((42972493483/2147483648), (7256051891/8589934592)), (5/17179869184), by norm_num⟩
  | 1 => ⟨((175669802295/137438953472), (880503197/68719476736)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((833328847027200/86009245502742241), (-21331851354720/86009245502742241)), 0, by norm_num⟩
  | 3 => ⟨((-70324135353/562949953421312), (14393453949/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((347529801749/144115188075855872), (-26672600693/144115188075855872)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-257157626471/4611686018427387904), (13163829675/2305843009213693952)), (19/4611686018427387904), by norm_num⟩
  | 6 => ⟨((52767215085/36893488147419103232), (-54074750255/295147905179352825856)), (13/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-370621037075/9444732965739290427392), (28526864929/4722366482869645213696)), (33/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((170560374759/151115727451828646838272), (-1918249263/9444732965739290427392)), (5/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-40637363851/1208925819614629174706176), (67021445849/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((318208709693/309485009821345068724781056), (-74017751051/309485009821345068724781056)), (125/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-159041537351/4951760157141521099596496896), (41245762855/4951760157141521099596496896)), (73/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((323389125781/316912650057057350374175801344), (-92616902443/316912650057057350374175801344)), (91/158456325028528675187087900672), by norm_num⟩
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
  | 0 => ⟨((359567191653/17179869184), (7256051891/8589934592)), (3/8589934592), by norm_num⟩
  | 1 => ⟨((175669802295/137438953472), (880503197/68719476736)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((833328847027200/86009245502742241), (-21331851354720/86009245502742241)), 0, by norm_num⟩
  | 3 => ⟨((-70324135353/562949953421312), (14393453949/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((347529801749/144115188075855872), (-26672600693/144115188075855872)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-257157626471/4611686018427387904), (13163829675/2305843009213693952)), (19/4611686018427387904), by norm_num⟩
  | 6 => ⟨((52767215085/36893488147419103232), (-54074750255/295147905179352825856)), (13/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-370621037075/9444732965739290427392), (28526864929/4722366482869645213696)), (33/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((170560374759/151115727451828646838272), (-1918249263/9444732965739290427392)), (5/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-40637363851/1208925819614629174706176), (67021445849/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((318208709693/309485009821345068724781056), (-74017751051/309485009821345068724781056)), (125/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-159041537351/4951760157141521099596496896), (41245762855/4951760157141521099596496896)), (73/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((323389125781/316912650057057350374175801344), (-92616902443/316912650057057350374175801344)), (91/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((479912707686400/86009245502742241), (-23729799168000/86009245502742241)), 0, by norm_num⟩
  | 1 => ⟨((-117210672617/281474976710656), (17404547917/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((419616097241/18014398509481984), (-5199805207/2251799813685248)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((-166811873043/144115188075855872), (20709119003/144115188075855872)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((248521468225/4611686018427387904), (-37107361421/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-44402880997/18446744073709551616), (62044968667/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 6 => ⟨((61665290509/590295810358705651712), (-49390667673/2361183241434822606848)), (5/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-5239862735/1180591620717411303424), (18952649239/18889465931478580854784)), (7/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((224259565951/1208925819614629174706176), (-56553730919/1208925819614629174706176)), (3/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-74010805915/9671406556917033397649408), (82484687465/38685626227668133590597632)), (1/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((386641828149/1237940039285380274899124224), (-59046861347/618970019642690137449562112)), (3/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-250229578097/19807040628566084398385987584), (83239564951/19807040628566084398385987584)), (5/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((321423484475/633825300114114700748351602688), (-57908020297/316912650057057350374175801344)), (13/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((117210672617/281474976710656), (-17404547917/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-419616097241/9007199254740992), (5199805207/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((62554452391/18014398509481984), (-31063678505/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((-248521468225/1152921504606846976), (18553680711/576460752303423488)), (3/1152921504606846976), by norm_num⟩
  | 4 => ⟨((222014404985/18446744073709551616), (-38778105417/18446744073709551616)), (3/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-369991743055/590295810358705651712), (74086001509/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 6 => ⟨((36679039145/1180591620717411303424), (-4145892021/590295810358705651712)), (3/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-224259565951/151115727451828646838272), (56553730919/151115727451828646838272)), (3/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((166524313309/2417851639229258349412352), (-46397636699/2417851639229258349412352)), (9/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-241651142593/77371252455336267181195264), (18452144171/19342813113834066795298816)), (1/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((86016417471/618970019642690137449562112), (-114454401807/2475880078570760549798248448)), (3/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-60266903339/9903520314283042199192993792), (43431015223/19807040628566084398385987584)), (5/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((41655567345/158456325028528675187087900672), (-129461792485/1267650600228229401496703205376)), (15/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((279744064827/9007199254740992), (-27732294437/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 1 => ⟨((-166811873043/36028797018963968), (20709119003/36028797018963968)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((248521468225/576460752303423488), (-18553680711/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 3 => ⟨((-296019206647/9223372036854775808), (51704140557/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((308326452545/147573952589676412928), (-61738334591/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-36679039145/295147905179352825856), (66334272337/2361183241434822606848)), (3/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((65409040069/9444732965739290427392), (-65979352739/37778931862957161709568)), (3/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-222032417745/604462909807314587353088), (61863515599/604462909807314587353088)), (3/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((181238356945/9671406556917033397649408), (-55356432513/9671406556917033397649408)), (11/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-143360695785/154742504910672534362390528), (95378668173/309485009821345068724781056)), (5/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((220978645577/4951760157141521099596496896), (-19905881977/1237940039285380274899124224)), (9/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-41655567345/19807040628566084398385987584), (129461792485/158456325028528675187087900672)), (7/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((246612665267/2535301200456458802993406410752), (-102887155445/2535301200456458802993406410752)), (3/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((333623746085/144115188075855872), (-20709119003/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 1 => ⟨((-248521468225/576460752303423488), (18553680711/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((222014404985/4611686018427387904), (-77556210835/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-154163226273/36893488147419103232), (61738334591/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 4 => ⟨((183395195725/590295810358705651712), (-82917840421/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-196227120207/9444732965739290427392), (98969029109/18889465931478580854784)), (9/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((194278365527/151115727451828646838272), (-108261152299/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-181238356945/2417851639229258349412352), (55356432513/2417851639229258349412352)), (5/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((80640391379/19342813113834066795298816), (-107301001695/77371252455336267181195264)), (11/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-276223306971/1237940039285380274899124224), (49764704943/618970019642690137449562112)), (5/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((114552810199/9903520314283042199192993792), (-89004982333/19807040628566084398385987584)), (5/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-369918997901/633825300114114700748351602688), (154330733167/633825300114114700748351602688)), (17/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((145897046919/5070602400912917605986812821504), (-65144796881/5070602400912917605986812821504)), (15/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((49704293645/288230376151711744), (-29685889137/1152921504606846976)), (5/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-44402880997/1152921504606846976), (15511242167/2305843009213693952)), (3/4611686018427387904), by norm_num⟩
  | 2 => ⟨((184995871527/36893488147419103232), (-37043000755/36893488147419103232)), (3/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-293432313161/590295810358705651712), (66334272337/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 4 => ⟨((392454240415/9444732965739290427392), (-24742257277/2361183241434822606848)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-233134038633/75557863725914323419136), (64956691379/75557863725914323419136)), (3/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((253733699723/1208925819614629174706176), (-77499005519/1208925819614629174706176)), (1/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-258049252413/19342813113834066795298816), (21460200339/4835703278458516698824704)), (1/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((124300488137/154742504910672534362390528), (-44788234449/154742504910672534362390528)), (5/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-114552810199/2475880078570760549798248448), (44502491167/2475880078570760549798248448)), (5/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((101727724423/39614081257132168796771975168), (-42440951621/39614081257132168796771975168)), (5/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-175076456303/1267650600228229401496703205376), (78173756257/1267650600228229401496703205376)), (17/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((293250412745/40564819207303340847894502572032), (-139726996075/40564819207303340847894502572032)), (1/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((236815365317/18446744073709551616), (-41363312445/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-61665290509/18446744073709551616), (49390667673/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 2 => ⟨((36679039145/73786976294838206464), (-66334272337/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-261636160277/4722366482869645213696), (65979352739/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((388556731055/75557863725914323419136), (-108261152299/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-63433424931/151115727451828646838272), (38749502759/302231454903657293676544)), (7/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((301057461149/9671406556917033397649408), (-50073800791/4835703278458516698824704)), (5/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-331467968365/154742504910672534362390528), (14929411483/19342813113834066795298816)), (3/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((343658430597/2475880078570760549798248448), (-133507473501/2475880078570760549798248448)), (7/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-339092414743/39614081257132168796771975168), (70734919369/19807040628566084398385987584)), (1/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((320973503223/633825300114114700748351602688), (-143318553139/633825300114114700748351602688)), (17/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-293250412745/10141204801825835211973625643008), (139726996075/10141204801825835211973625643008)), (1/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((259847091379/162259276829213363391578010288128), (-131782825897/162259276829213363391578010288128)), (1/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((140949235449/147573952589676412928), (-14111619335/73786976294838206464)), (3/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-5239862735/18446744073709551616), (75810596957/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 2 => ⟨((224259565951/4722366482869645213696), (-56553730919/4722366482869645213696)), (5/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-111016208873/18889465931478580854784), (61863515599/37778931862957161709568)), (3/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((362476713891/604462909807314587353088), (-110712865027/604462909807314587353088)), (5/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((-129024626207/2417851639229258349412352), (21460200339/1208925819614629174706176)), (1/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((165733984183/38685626227668133590597632), (-119435291863/77371252455336267181195264)), (3/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((-392752492111/1237940039285380274899124224), (38144992429/309485009821345068724781056)), (1/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((108993990453/4951760157141521099596496896), (-90944896331/9903520314283042199192993792)), (5/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-14329174251/9903520314283042199192993792), (102370395099/158456325028528675187087900672)), (3/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((115205519293/1267650600228229401496703205376), (-27446374229/633825300114114700748351602688)), (13/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-222726078325/40564819207303340847894502572032), (14119588489/5070602400912917605986812821504)), (7/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((104080208047/324518553658426726783156020576256), (-28029448213/162259276829213363391578010288128)), (7/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5239862735/73786976294838206464), (-18952649239/1180591620717411303424)), (1/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-224259565951/9444732965739290427392), (56553730919/9444732965739290427392)), (3/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((166524313309/37778931862957161709568), (-92795273399/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-362476713891/604462909807314587353088), (55356432513/302231454903657293676544)), (5/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((322561565517/4835703278458516698824704), (-107301001695/4835703278458516698824704)), (5/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-248600976275/38685626227668133590597632), (44788234449/19342813113834066795298816)), (9/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((343658430597/618970019642690137449562112), (-133507473501/618970019642690137449562112)), (7/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-108993990453/2475880078570760549798248448), (90944896331/4951760157141521099596496896)), (5/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((128962568259/39614081257132168796771975168), (-57583347243/39614081257132168796771975168)), (13/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((-36001724779/158456325028528675187087900672), (137231871145/1267650600228229401496703205376)), (1/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((306248357697/20282409603651670423947251286016), (-155315473379/20282409603651670423947251286016)), (9/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((-156120312071/162259276829213363391578010288128), (84088344639/162259276829213363391578010288128)), (21/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((153469088093/2596148429267413814265248164610048), (-43809146401/1298074214633706907132624082305024)), (11/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((199341836401/37778931862957161709568), (-50269983039/37778931862957161709568)), (5/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((-74010805915/37778931862957161709568), (82484687465/151115727451828646838272)), (9/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((120825571297/302231454903657293676544), (-18452144171/151115727451828646838272)), (1/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-143360695785/2417851639229258349412352), (95378668173/4835703278458516698824704)), (9/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((69055826743/9671406556917033397649408), (-49764704943/19342813113834066795298816)), (5/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-229105620399/309485009821345068724781056), (44502491167/154742504910672534362390528)), (9/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((339092414743/4951760157141521099596496896), (-70734919369/2475880078570760549798248448)), (15/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((-14329174251/2475880078570760549798248448), (102370395099/39614081257132168796771975168)), (11/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((36001724779/79228162514264337593543950336), (-137231871145/633825300114114700748351602688)), (15/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((-340275952997/10141204801825835211973625643008), (172572748199/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((190813714753/81129638414606681695789005144064), (-102774643447/81129638414606681695789005144064)), (13/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((-204625450791/1298074214633706907132624082305024), (58412195201/649037107316853453566312041152512)), (15/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((52759295005/5192296858534827628530496329220096), (-31874442219/5192296858534827628530496329220096)), (17/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((14802161183/37778931862957161709568), (-16496937493/151115727451828646838272)), (7/604462909807314587353088), by norm_num⟩
  | 1 => ⟨((-386641828149/2417851639229258349412352), (59046861347/1208925819614629174706176)), (13/2417851639229258349412352), by norm_num⟩
  | 2 => ⟨((86016417471/2417851639229258349412352), (-7153400113/604462909807314587353088)), (13/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((-220978645577/38685626227668133590597632), (79623527909/38685626227668133590597632)), (1/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((114552810199/154742504910672534362390528), (-44502491167/154742504910672534362390528)), (5/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-203455448847/2475880078570760549798248448), (42440951621/1237940039285380274899124224)), (5/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((320973503223/39614081257132168796771975168), (-143318553139/39614081257132168796771975168)), (15/39614081257132168796771975168), by norm_num⟩
  | 7 => ⟨((-115205519293/158456325028528675187087900672), (27446374229/79228162514264337593543950336)), (3/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((306248357697/5070602400912917605986812821504), (-155315473379/5070602400912917605986812821504)), (17/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-190813714753/40564819207303340847894502572032), (102774643447/40564819207303340847894502572032)), (13/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((112543997935/324518553658426726783156020576256), (-64253414721/324518553658426726783156020576256)), (1/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((-31655577003/1298074214633706907132624082305024), (152997322651/10384593717069655257060992658440192)), (5/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((273389041891/166153499473114484112975882535043072), (-87263823071/83076749736557242056487941267521536)), (23/166153499473114484112975882535043072), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/879819987), (-45120/293273329)), 0, by norm_num⟩
  | 1 => ⟨((-59989088460800/258027736508226723), (988741632000/86009245502742241)), 0, by norm_num⟩
  | 2 => ⟨((312561793645/36028797018963968), (-23206063889/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((-93248021609/288230376151711744), (36976392583/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 4 => ⟨((444831661447/36893488147419103232), (-55224317341/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-265089566107/590295810358705651712), (9895296379/147573952589676412928)), (1/147573952589676412928), by norm_num⟩
  | 6 => ⟨((315753820423/18889465931478580854784), (-13787770815/4722366482869645213696)), (3/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-46983078483/75557863725914323419136), (75261969787/604462909807314587353088)), (9/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((447134953387/19342813113834066795298816), (-101080795941/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-265789115201/309485009821345068724781056), (16756661013/77371252455336267181195264)), (7/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((315779438571/9903520314283042199192993792), (-87983666629/9903520314283042199192993792)), (5/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-374925409115/316912650057057350374175801344), (28628781259/79228162514264337593543950336)), (7/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((111213145821/2535301200456458802993406410752), (-4624420275/316912650057057350374175801344)), (9/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179837083015/8589934592), (14509460665/17179869184)), (7/17179869184), by norm_num⟩
  | 1 => ⟨((351275697991/274877906944), (1762586359/137438953472)), (3/274877906944), by norm_num⟩
  | 2 => ⟨((341200590513/35184372088832), (-8749023983/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-282025041581/2251799813685248), (7232836733/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((349267425427/144115188075855872), (-26888320683/144115188075855872)), (17/144115188075855872), by norm_num⟩
  | 5 => ⟨((-129614319353/2305843009213693952), (13318443681/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((106767843531/73786976294838206464), (-54936485931/295147905179352825856)), (53/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-376493921885/9444732965739290427392), (7278712267/1180591620717411303424)), (67/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((348107233165/302231454903657293676544), (-62963363853/302231454903657293676544)), (81/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-166702410329/4835703278458516698824704), (17279007119/2417851639229258349412352)), (103/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((82019204287/77371252455336267181195264), (-76767240633/309485009821345068724781056)), (63/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-329799493737/9903520314283042199192993792), (86070123367/9903520314283042199192993792)), (147/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((337290769009/316912650057057350374175801344), (-48620661359/158456325028528675187087900672)), (183/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-333399246555/288230376151711744), (24753134815/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 1 => ⟨((298393669149/2305843009213693952), (-14790557033/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-177932664579/18446744073709551616), (22089726937/18446744073709551616)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((353452754809/590295810358705651712), (-26387457011/295147905179352825856)), (5/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-315753820423/9444732965739290427392), (13787770815/2361183241434822606848)), (5/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((131552619753/75557863725914323419136), (-52683378851/151115727451828646838272)), (5/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-208662978247/2417851639229258349412352), (94342076211/4835703278458516698824704)), (9/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((318946938241/77371252455336267181195264), (-80431972863/77371252455336267181195264)), (5/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-14802161183/77371252455336267181195264), (16496937493/309485009821345068724781056)), (7/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((343681625021/39614081257132168796771975168), (-104972197951/39614081257132168796771975168)), (3/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-122334460403/316912650057057350374175801344), (81389796841/633825300114114700748351602688)), (5/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((342851716773/20282409603651670423947251286016), (-7721069373/1267650600228229401496703205376)), (15/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-236973894229/324518553658426726783156020576256), (23015429775/81129638414606681695789005144064)), (3/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179837073079/8589934592), (3627365535/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((175637866781/137438953472), (440646149/34359738368)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((341200251133/35184372088832), (-4374490925/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-141011846633/1125899906842624), (7232736073/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((174631303703/72057594037927936), (-3360934893/18014398509481984)), (9/72057594037927936), by norm_num⟩
  | 5 => ⟨((-259220609371/4611686018427387904), (26635279593/4611686018427387904)), (21/4611686018427387904), by norm_num⟩
  | 6 => ⟨((427045902569/295147905179352825856), (-13732681937/73786976294838206464)), (27/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-376454987933/9444732965739290427392), (14554969945/2361183241434822606848)), (17/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((348049412223/302231454903657293676544), (-31473626781/151115727451828646838272)), (41/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-333320914011/9671406556917033397649408), (34545200249/4835703278458516698824704)), (13/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((163978674951/154742504910672534362390528), (-76727499521/309485009821345068724781056)), (127/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-41204010709/1237940039285380274899124224), (86009802513/9903520314283042199192993792)), (37/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((168529674595/158456325028528675187087900672), (-97151418695/316912650057057350374175801344)), (23/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((135567744441/73786976294838206464), (-8415134071/36893488147419103232)), (3/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-50493250687/147573952589676412928), (30157093727/590295810358705651712)), (7/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((360861509055/9444732965739290427392), (-63029809441/9444732965739290427392)), (5/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-250576418577/75557863725914323419136), (50174646525/75557863725914323419136)), (5/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((74522492231/302231454903657293676544), (-67387197295/1208925819614629174706176)), (7/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-318946938241/19342813113834066795298816), (80431972863/19342813113834066795298816)), (1/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((315779438571/309485009821345068724781056), (-43991833315/154742504910672534362390528)), (9/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-294584250019/4951760157141521099596496896), (11247021209/618970019642690137449562112)), (9/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((65536318073/19807040628566084398385987584), (-43601676879/39614081257132168796771975168)), (5/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((-112243121563/633825300114114700748351602688), (80887393431/1267650600228229401496703205376)), (9/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((372387548075/40564819207303340847894502572032), (-144668415729/40564819207303340847894502572032)), (9/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-300632582421/649037107316853453566312041152512), (125424341875/649037107316853453566312041152512)), (15/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((237140596897/10384593717069655257060992658440192), (-105886146041/10384593717069655257060992658440192)), (13/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179837073095/8589934592), (1813682767/2147483648)), (9/17179869184), by norm_num⟩
  | 1 => ⟨((87818933367/68719476736), (1762584603/137438953472)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((341200252477/35184372088832), (-8748982085/35184372088832)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-141011850367/1125899906842624), (14465473641/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 4 => ⟨((349262642941/144115188075855872), (-26887487177/144115188075855872)), (19/144115188075855872), by norm_num⟩
  | 5 => ⟨((-129610342707/2305843009213693952), (26635298769/4611686018427387904)), (11/2305843009213693952), by norm_num⟩
  | 6 => ⟨((53380775465/36893488147419103232), (-6866351457/36893488147419103232)), (55/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-23528471863/590295810358705651712), (14555012849/2361183241434822606848)), (69/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((87012603057/75557863725914323419136), (-7868448277/37778931862957161709568)), (83/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-333322626705/9671406556917033397649408), (17272754405/2417851639229258349412352)), (105/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((163980095497/154742504910672534362390528), (-76728603253/309485009821345068724781056)), (1/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-329636672961/9903520314283042199192993792), (86011716337/9903520314283042199192993792)), (149/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((337066586147/316912650057057350374175801344), (-24288662521/79228162514264337593543950336)), (185/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-72172301811/9444732965739290427392), (393936309/295147905179352825856)), (3/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((75172925573/37778931862957161709568), (-30104787915/75557863725914323419136)), (7/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-357707962709/1208925819614629174706176), (40432318377/604462909807314587353088)), (1/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((159473469121/4835703278458516698824704), (-80431972863/9671406556917033397649408)), (1/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((-236834578929/77371252455336267181195264), (65987749973/77371252455336267181195264)), (3/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((309313462521/1237940039285380274899124224), (-94474978155/1237940039285380274899124224)), (5/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((-183501690605/9903520314283042199192993792), (61042347631/9903520314283042199192993792)), (13/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((202037618813/158456325028528675187087900672), (-145597308177/316912650057057350374175801344)), (15/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((-13091749737/158456325028528675187087900672), (10171997981/316912650057057350374175801344)), (5/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((206684900415/40564819207303340847894502572032), (-2694663595/1267650600228229401496703205376)), (11/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-195640992441/649037107316853453566312041152512), (87356070485/649037107316853453566312041152512)), (11/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((178743108721/10384593717069655257060992658440192), (-85166930941/10384593717069655257060992658440192)), (21/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((-158382989031/166153499473114484112975882535043072), (160649540141/332306998946228968225951765070086144)), (5/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179837073095/8589934592), (1813682767/2147483648)), (5/8589934592), by norm_num⟩
  | 1 => ⟨((351275733469/274877906944), (1762584603/137438953472)), (3/137438953472), by norm_num⟩
  | 2 => ⟨((341200252467/35184372088832), (-8748982083/35184372088832)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-70505925165/562949953421312), (7232736811/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((87315660625/36028797018963968), (-13443743527/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 5 => ⟨((-129610342131/2305843009213693952), (26635298417/4611686018427387904)), (23/4611686018427387904), by norm_num⟩
  | 6 => ⟨((427046198251/295147905179352825856), (-54930809837/295147905179352825856)), (7/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-188227768883/4722366482869645213696), (58220047057/9444732965739290427392)), (35/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((348050387257/302231454903657293676544), (-62947576515/302231454903657293676544)), (21/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-333322577427/9671406556917033397649408), (69090997061/9671406556917033397649408)), (53/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((327960097705/309485009821345068724781056), (-38364280799/154742504910672534362390528)), (129/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-164818251249/4951760157141521099596496896), (86011635115/9903520314283042199192993792)), (75/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((337066284055/316912650057057350374175801344), (-97154496877/316912650057057350374175801344)), (93/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((289056939563/4835703278458516698824704), (-65345161013/4835703278458516698824704)), (1/604462909807314587353088), by norm_num⟩
  | 1 => ⟨((-48325293673/2417851639229258349412352), (97493300439/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 2 => ⟨((287072216883/77371252455336267181195264), (-39992575741/38685626227668133590597632)), (1/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((-156218920465/309485009821345068724781056), (5964329429/38685626227668133590597632)), (5/309485009821345068724781056), by norm_num⟩
  | 4 => ⟨((278032864553/4951760157141521099596496896), (-92488405501/4951760157141521099596496896)), (5/2475880078570760549798248448), by norm_num⟩
  | 5 => ⟨((-214282322985/39614081257132168796771975168), (38605346865/19807040628566084398385987584)), (9/39614081257132168796771975168), by norm_num⟩
  | 6 => ⟨((296217367787/633825300114114700748351602688), (-28769287219/158456325028528675187087900672)), (13/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-375790728027/10141204801825835211973625643008), (156780427345/10141204801825835211973625643008)), (9/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((222319309591/81129638414606681695789005144064), (-49634130957/40564819207303340847894502572032)), (3/20282409603651670423947251286016), by norm_num⟩
  | 9 => ⟨((-62063579417/324518553658426726783156020576256), (118287404085/1298074214633706907132624082305024)), (15/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((263971648385/20769187434139310514121985316880384), (-133874616785/20769187434139310514121985316880384)), (17/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((-269136699597/332306998946228968225951765070086144), (144960378637/332306998946228968225951765070086144)), (19/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((132283119703/2658455991569831745807614120560689152), (-2360088695/83076749736557242056487941267521536)), (5/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179837073095/8589934592), (1813682767/2147483648)), (11/17179869184), by norm_num⟩
  | 1 => ⟨((351275733469/274877906944), (1762584603/137438953472)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((341200252467/35184372088832), (-8748982083/35184372088832)), (5/35184372088832), by norm_num⟩
  | 3 => ⟨((-282023700661/2251799813685248), (7232736811/1125899906842624)), (9/2251799813685248), by norm_num⟩
  | 4 => ⟨((87315660627/36028797018963968), (-26887487057/144115188075855872)), (21/144115188075855872), by norm_num⟩
  | 5 => ⟨((-259220684287/4611686018427387904), (13317649213/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((427046198389/295147905179352825856), (-54930809891/295147905179352825856)), (57/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-94113884529/2361183241434822606848), (58220047203/9444732965739290427392)), (71/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((348050388085/302231454903657293676544), (-62947576885/302231454903657293676544)), (85/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-333322579277/9671406556917033397649408), (34545498971/4835703278458516698824704)), (107/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((163980050819/154742504910672534362390528), (-76728563593/309485009821345068724781056)), (65/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-329636510519/9903520314283042199192993792), (86011639435/9903520314283042199192993792)), (151/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((21066643739/19807040628566084398385987584), (-12144313235/39614081257132168796771975168)), (187/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-232517980209/309485009821345068724781056), (64785042841/309485009821345068724781056)), (1/38685626227668133590597632), by norm_num⟩
  | 1 => ⟨((189797404907/618970019642690137449562112), (-115941320733/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 2 => ⟨((-337794653901/4951760157141521099596496896), (14046041363/618970019642690137449562112)), (7/2475880078570760549798248448), by norm_num⟩
  | 3 => ⟨((216951040559/19807040628566084398385987584), (-78172292113/19807040628566084398385987584)), (9/19807040628566084398385987584), by norm_num⟩
  | 4 => ⟨((-56232472841/39614081257132168796771975168), (87382758103/158456325028528675187087900672)), (11/158456325028528675187087900672), by norm_num⟩
  | 5 => ⟨((199747225437/1267650600228229401496703205376), (-41667413575/633825300114114700748351602688)), (5/633825300114114700748351602688), by norm_num⟩
  | 6 => ⟨((-78780842527/5070602400912917605986812821504), (70353198957/10141204801825835211973625643008)), (1/1267650600228229401496703205376), by norm_num⟩
  | 7 => ⟨((226211516715/162259276829213363391578010288128), (-107784522491/162259276829213363391578010288128)), (3/40564819207303340847894502572032), by norm_num⟩
  | 8 => ⟨((-150333304149/1298074214633706907132624082305024), (152484659667/2596148429267413814265248164610048)), (9/1298074214633706907132624082305024), by norm_num⟩
  | 9 => ⟨((187335902347/20769187434139310514121985316880384), (-100901450367/20769187434139310514121985316880384)), (7/10384593717069655257060992658440192), by norm_num⟩
  | 10 => ⟨((-220985492937/332306998946228968225951765070086144), (126164635925/332306998946228968225951765070086144)), (1/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((62157231097/1329227995784915872903807060280344576), (-37552190015/1329227995784915872903807060280344576)), (21/5316911983139663491615228241121378304), by norm_num⟩
  | 12 => ⟨((-268406193553/85070591730234615865843651857942052864), (171346667177/85070591730234615865843651857942052864)), (23/85070591730234615865843651857942052864), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179837073095/8589934592), (1813682767/2147483648)), (3/4294967296), by norm_num⟩
  | 1 => ⟨((351275733469/274877906944), (1762584603/137438953472)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((341200252467/35184372088832), (-8748982083/35184372088832)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-282023700661/2251799813685248), (7232736811/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 4 => ⟨((87315660627/36028797018963968), (-26887487057/144115188075855872)), (11/72057594037927936), by norm_num⟩
  | 5 => ⟨((-129610342143/2305843009213693952), (13317649213/2305843009213693952)), (25/4611686018427387904), by norm_num⟩
  | 6 => ⟨((26690387399/18446744073709551616), (-54930809889/295147905179352825856)), (29/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-376455538103/9444732965739290427392), (58220047197/9444732965739290427392)), (9/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((174025194025/151115727451828646838272), (-62947576867/302231454903657293676544)), (43/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-166661289595/4835703278458516698824704), (69090997895/9671406556917033397649408)), (27/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((40995012679/38685626227668133590597632), (-19182140869/77371252455336267181195264)), (131/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-41204563757/1237940039285380274899124224), (86011639155/9903520314283042199192993792)), (19/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((42133287353/39614081257132168796771975168), (-48577252621/158456325028528675187087900672)), (47/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((430600905696549/524288), (484824107515275/524288)), (432981/262144), by norm_num⟩
  | 1 => ⟨((132827581793/128), (76305577423/64)), (35/16), by norm_num⟩
  | 2 => ⟨((169885485251/256), (198973790735/256)), (375/256), by norm_num⟩
  | 3 => ⟨((1144641959/4), (21846397863/64)), (339/512), by norm_num⟩
  | 4 => ⟨((95787419445/1024), (116279657533/1024)), (463/2048), by norm_num⟩
  | 5 => ⟨((202425828825/8192), (124947687697/4096)), (1/16), by norm_num⟩
  | 6 => ⟨((89975718235/16384), (225770865503/32768)), (477/32768), by norm_num⟩
  | 7 => ⟨((138366420071/131072), (176324776475/131072)), (385/131072), by norm_num⟩
  | 8 => ⟨((23474569637/131072), (242947682015/1048576)), (549/1048576), by norm_num⟩
  | 9 => ⟨((228435800487/8388608), (37482954683/1048576)), (703/8388608), by norm_num⟩
  | 10 => ⟨((126028698255/33554432), (20974066441/4194304)), (205/16777216), by norm_num⟩
  | 11 => ⟨((127375447447/268435456), (171931874323/268435456)), (439/268435456), by norm_num⟩
  | 12 => ⟨((59432805889/1073741824), (162604114757/2147483648)), (109/536870912), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1611246972038413/10141204801825835211973625643008), (1100136108115/10141204801825835211973625643008)), (911/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1814913949229203/633825300114114700748351602688), (337849107949/158456325028528675187087900672)), (35/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((482612757874189/9903520314283042199192993792), (1524511366381/39614081257132168796771975168)), (79/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((966406528429473/1237940039285380274899124224), (1623341942773/2475880078570760549798248448)), (673/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1814527140078293/154742504910672534362390528), (1627310666191/154742504910672534362390528)), (1349/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((795116140035577/4835703278458516698824704), (95614589697/604462909807314587353088)), (317/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((647216868404035/302231454903657293676544), (671424703277/302231454903657293676544)), (557/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1945811251829007/75557863725914323419136), (547530746233/18889465931478580854784)), (227/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1341138121742739/4722366482869645213696), (1649619053801/4722366482869645213696)), (1369/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((840766857516531/295147905179352825856), (2279707373565/590295810358705651712)), (1891/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1898788651147359/73786976294838206464), (716741555261/18446744073709551616)), (1189/36893488147419103232), by norm_num⟩
  | 7 => ⟨((238458910471415/1152921504606846976), (1624674477273/4611686018427387904)), (337/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1679279598999819/1152921504606846976), (3279636879451/1152921504606846976)), (1361/576460752303423488), by norm_num⟩
  | 5 => ⟨((1269620596772181/144115188075855872), (2904135311823/144115188075855872)), (603/36028797018963968), by norm_num⟩
  | 4 => ⟨((802510208231595/18014398509481984), (4426068327269/36028797018963968)), (1839/18014398509481984), by norm_num⟩
  | 3 => ⟨((1632444537842003/9007199254740992), (5657040061753/9007199254740992)), (4705/9007199254740992), by norm_num⟩
  | 2 => ⟨((1259383264342385/2251799813685248), (1462045887883/562949953421312)), (4871/2251799813685248), by norm_num⟩
  | 1 => ⟨((1331847135998613/1125899906842624), (2316530096135/281474976710656)), (3867/562949953421312), by norm_num⟩
  | 0 => ⟨((1561453768188959/1125899906842624), (5151643910839/281474976710656)), (8635/562949953421312), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1561453768188959/1125899906842624), (5151643910839/281474976710656)), (32939913036155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2165124292502933/1125899906842624), (57156439914843/1125899906842624)), (48535/1125899906842624), by norm_num⟩
  | 2 => ⟨((2080334279669399/562949953421312), (54956393450483/281474976710656)), (47899/281474976710656), by norm_num⟩
  | 3 => ⟨((479140049241351/35184372088832), (50771684271051/35184372088832)), (23295/17592186044416), by norm_num⟩
  | 4 => ⟨((403228424629427/2199023255552), (172851935798929/4398046511104)), (350847/8796093022208), by norm_num⟩
  | 5 => ⟨((1102220284833565/34359738368), (495239858127753/34359738368)), (610335/34359738368), by norm_num⟩
  | 6 => ⟨((430600905696549/524288), (484824107515275/524288)), (432981/262144), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((179837073095/8589934592), (1813682767/2147483648)), (3/4294967296), by norm_num⟩, 0, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/3276529), (-541440/3276529)), 0, by norm_num⟩
  | 1 => ⟨((-2390975283200/10735642287841), (1219756032000/10735642287841)), 0, by norm_num⟩
  | 2 => ⟨((295446072197/4398046511104), (-252714948281/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-40343831067/2199023255552), (111288890899/4398046511104)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((148348338339/35184372088832), (-11231364853/1099511627776)), (5/35184372088832), by norm_num⟩
  | 5 => ⟨((-42607164673/70368744177664), (33953091977/8796093022208)), (5/70368744177664), by norm_num⟩
  | 6 => ⟨((-31181214257/281474976710656), (-193798201721/140737488355328)), (5/140737488355328), by norm_num⟩
  | 7 => ⟨((85488404393/562949953421312), (32667741573/70368744177664)), (9/562949953421312), by norm_num⟩
  | 8 => ⟨((-101964381635/1125899906842624), (-41390161971/281474976710656)), (1/140737488355328), by norm_num⟩
  | 9 => ⟨((194929766309/4503599627370496), (48491472647/1125899906842624)), (15/4503599627370496), by norm_num⟩
  | 10 => ⟨((-332155564221/18014398509481984), (-202301634227/18014398509481984)), (13/9007199254740992), by norm_num⟩
  | 11 => ⟨((65451446631/9007199254740992), (42102910259/18014398509481984)), (23/36028797018963968), by norm_num⟩
  | 12 => ⟨((-387842424311/144115188075855872), (-14633396319/72057594037927936)), (5/18014398509481984), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (423/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (423/1280)))⁻¹=value ((2252800/3276529), (-541440/3276529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/3276529), (-541440/3276529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/9420529), (-541440/9420529)), 0, by norm_num⟩
  | 1 => ⟨((-7424140083200/88746366639841), (2106851328000/88746366639841)), 0, by norm_num⟩
  | 2 => ⟨((145971102485/8796093022208), (-128546640487/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-226400282819/70368744177664), (139752210289/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((21370916213/35184372088832), (-141475275923/281474976710656)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((-249951016529/2251799813685248), (273053517341/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 6 => ⟨((175099996845/9007199254740992), (-254304047059/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 7 => ⟨((-14427499891/4503599627370496), (57552715469/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 8 => ⟨((17221799941/36028797018963968), (-203447069705/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 9 => ⟨((-33522425397/576460752303423488), (175988317233/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 10 => ⟨((3731780585/1152921504606846976), (-149239203451/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 11 => ⟨((21978326309/18446744073709551616), (496584137921/36893488147419103232)), (31/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-93394891583/147573952589676412928), (-101295177133/36893488147419103232)), (15/73786976294838206464), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (423/1280)))⁻¹=value ((3891200/9420529), (-541440/9420529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/9420529), (-541440/9420529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8472938086400/30866636463841), (-3326607360000/30866636463841)), 0, by norm_num⟩
  | 1 => ⟨((-305791896235/2199023255552), (98821117907/1099511627776)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((111230260477/2199023255552), (-6893071505/137438953472)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-133075288915/8796093022208), (25638594439/1099511627776)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((126977422125/35184372088832), (-170859632903/17592186044416)), (3/17592186044416), by norm_num⟩
  | 5 => ⟨((-17398097703/35184372088832), (263091813399/70368744177664)), (3/35184372088832), by norm_num⟩
  | 6 => ⟨((-36653089159/281474976710656), (-379649401971/281474976710656)), (5/140737488355328), by norm_num⟩
  | 7 => ⟨((10911480235/70368744177664), (257744887867/562949953421312)), (5/281474976710656), by norm_num⟩
  | 8 => ⟨((-205005125767/2251799813685248), (-327942435303/2251799813685248)), (17/2251799813685248), by norm_num⟩
  | 9 => ⟨((97595830129/2251799813685248), (192590981859/4503599627370496)), (1/281474976710656), by norm_num⟩
  | 10 => ⟨((-332213873293/18014398509481984), (-201135702949/18014398509481984)), (27/18014398509481984), by norm_num⟩
  | 11 => ⟨((261762860105/36028797018963968), (41860437535/18014398509481984)), (3/4503599627370496), by norm_num⟩
  | 12 => ⟨((-193875609181/72057594037927936), (-112777767/562949953421312)), (41/144115188075855872), by norm_num⟩
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
  | 0 => ⟨((27/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((204800/697827), (-60160/2093481)), 0, by norm_num⟩
  | 1 => ⟨((-186934067200/4382662697361), (12320768000/1460887565787)), 0, by norm_num⟩
  | 2 => ⟨((6257146593280000/1019446787370444849), (-16977796530176000/9175021086334003641)), 0, by norm_num⟩
  | 3 => ⟨((-246031239027/281474976710656), (25313441603/70368744177664)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((138592293573/1125899906842624), (-1149573865/17592186044416)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((-38560163619/2251799813685248), (204600074503/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((84654303401/36028797018963968), (-68911311505/36028797018963968)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((-91457050739/288230376151711744), (90627835039/288230376151711744)), (5/576460752303423488), by norm_num⟩
  | 8 => ⟨((193893487137/4611686018427387904), (-29225867357/576460752303423488)), (7/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-100370944905/18446744073709551616), (74190124209/9223372036854775808)), (5/18446744073709551616), by norm_num⟩
  | 10 => ⟨((25193136601/36893488147419103232), (-185725384035/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-1514863683/18446744073709551616), (114806059709/590295810358705651712)), (11/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((87420709705/9444732965739290427392), (-280692826765/9444732965739290427392)), (15/9444732965739290427392), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (423/1280)))⁻¹=value ((204800/697827), (-60160/2093481)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((204800/697827), (-60160/2093481))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((340691647741/4398046511104), (-173801801925/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-215626167261/4398046511104), (163983135571/4398046511104)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((44117309907/2199023255552), (-196579935089/8796093022208)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-56231864891/8796093022208), (95401954713/8796093022208)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((54968757543/35184372088832), (-326334004045/70368744177664)), (7/70368744177664), by norm_num⟩
  | 5 => ⟨((-7047557813/35184372088832), (255358110023/140737488355328)), (3/70368744177664), by norm_num⟩
  | 6 => ⟨((-41463602315/562949953421312), (-186120385061/281474976710656)), (3/140737488355328), by norm_num⟩
  | 7 => ⟨((44458326157/562949953421312), (15895303165/70368744177664)), (11/1125899906842624), by norm_num⟩
  | 8 => ⟨((-205986813709/4503599627370496), (-324877738383/4503599627370496)), (9/2251799813685248), by norm_num⟩
  | 9 => ⟨((195429049581/9007199254740992), (191252298777/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 10 => ⟨((-332259881029/36028797018963968), (-49998110807/9007199254740992)), (29/36028797018963968), by norm_num⟩
  | 11 => ⟨((32714621871/9007199254740992), (20810734207/18014398509481984)), (13/36028797018963968), by norm_num⟩
  | 12 => ⟨((-387658678479/288230376151711744), (-14239853549/144115188075855872)), (43/288230376151711744), by norm_num⟩
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
  | 0 => ⟨((35/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/31538929), (-541440/31538929)), 0, by norm_num⟩
  | 1 => ⟨((-25543533363200/994704042467041), (3881041920000/994704042467041)), 0, by norm_num⟩
  | 2 => ⟨((101495043155/35184372088832), (-23355534525/35184372088832)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-5666575177/17592186044416), (56404184845/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((321947994101/9007199254740992), (-127457652557/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((-283930066277/72057594037927936), (137979571273/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((248645482667/576460752303423488), (-144934365015/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-216090731193/4611686018427387904), (148833987173/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 8 => ⟨((186227463485/36893488147419103232), (-75071806373/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-2484201153/4611686018427387904), (74641749185/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 10 => ⟨((67142685155/1180591620717411303424), (-146631111303/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-112009584787/18889465931478580854784), (17815431791/2361183241434822606848)), (19/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((184081534193/302231454903657293676544), (-137259523329/151115727451828646838272)), (5/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (423/1280)))⁻¹=value ((7168000/31538929), (-541440/31538929)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/31538929), (-541440/31538929))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((297787471905/17592186044416), (-181398094013/17592186044416)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-108523779601/8796093022208), (187053491399/17592186044416)), (3/17592186044416), by norm_num⟩
  | 2 => ⟨((193047130433/35184372088832), (-237067263003/35184372088832)), (5/35184372088832), by norm_num⟩
  | 3 => ⟨((-128943145707/70368744177664), (59593976051/17592186044416)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((63980671913/140737488355328), (-104250002853/70368744177664)), (11/281474976710656), by norm_num⟩
  | 5 => ⟨((-30015995675/562949953421312), (331051840017/562949953421312)), (9/562949953421312), by norm_num⟩
  | 6 => ⟨((-30489441769/1125899906842624), (-487066318881/2251799813685248)), (17/2251799813685248), by norm_num⟩
  | 7 => ⟨((120518951945/4503599627370496), (334751536923/4503599627370496)), (1/281474976710656), by norm_num⟩
  | 8 => ⟨((-68961731173/4503599627370496), (-214612027313/9007199254740992)), (7/4503599627370496), by norm_num⟩
  | 9 => ⟨((260859147009/36028797018963968), (126631708971/18014398509481984)), (3/4503599627370496), by norm_num⟩
  | 10 => ⟨((-13845608831/4503599627370496), (-16572561363/9007199254740992)), (21/72057594037927936), by norm_num⟩
  | 11 => ⟨((87222781585/72057594037927936), (55181155967/144115188075855872)), (9/72057594037927936), by norm_num⟩
  | 12 => ⟨((-258376594959/576460752303423488), (-9364152659/288230376151711744)), (15/288230376151711744), by norm_num⟩
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
  | 0 => ⟨((43/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/47513329), (-541440/47513329)), 0, by norm_num⟩
  | 1 => ⟨((-38629761843200/2257516432662241), (4768137216000/2257516432662241)), 0, by norm_num⟩
  | 2 => ⟨((110742794313/70368744177664), (-82538059903/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-324649276265/2251799813685248), (81383940489/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((236979973831/18014398509481984), (-75134927941/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((-86134119803/72057594037927936), (133011714073/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((124685356737/1152921504606846976), (-114317411025/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-179668507935/18446744073709551616), (96119901643/18446744073709551616)), (1/9223372036854775808), by norm_num⟩
  | 8 => ⟨((128821921843/147573952589676412928), (-39725695447/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-45942443285/590295810358705651712), (8096991795/147573952589676412928)), (1/590295810358705651712), by norm_num⟩
  | 10 => ⟨((65169315599/9444732965739290427392), (-208848490943/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-183742066705/302231454903657293676544), (83359532547/151115727451828646838272)), (7/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((32155982285/604462909807314587353088), (-32994532533/604462909807314587353088)), (3/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (423/1280)))⁻¹=value ((8806400/47513329), (-541440/47513329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/47513329), (-541440/47513329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((212506213451/70368744177664), (-37014839013/17592186044416)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-171239154009/70368744177664), (81751891423/35184372088832)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((20273898299/17592186044416), (-216813386695/140737488355328)), (5/140737488355328), by norm_num⟩
  | 3 => ⟨((-112321401409/281474976710656), (112319601547/140737488355328)), (7/281474976710656), by norm_num⟩
  | 4 => ⟨((14047190439/140737488355328), (-100205381933/281474976710656)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((-23424442419/2251799813685248), (80593950419/562949953421312)), (5/1125899906842624), by norm_num⟩
  | 6 => ⟨((-33037158893/4503599627370496), (-239179663411/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 7 => ⟨((61153614687/9007199254740992), (165297372773/9007199254740992)), (17/18014398509481984), by norm_num⟩
  | 8 => ⟨((-138473110635/36028797018963968), (-53175898559/9007199254740992)), (15/36028797018963968), by norm_num⟩
  | 9 => ⟨((261119556999/144115188075855872), (7861447713/4503599627370496)), (13/72057594037927936), by norm_num⟩
  | 10 => ⟨((-221545977503/288230376151711744), (-131846375475/288230376151711744)), (11/144115188075855872), by norm_num⟩
  | 11 => ⟨((348822881603/1152921504606846976), (109742685959/1152921504606846976)), (19/576460752303423488), by norm_num⟩
  | 12 => ⟨((-1009036303/9007199254740992), (-9236412651/1152921504606846976)), (1/72057594037927936), by norm_num⟩
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
  | 0 => ⟨((51/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/22254843), (-60160/7418281)), 0, by norm_num⟩
  | 1 => ⟨((-6044482764800/495278036954649), (209453056000/165092678984883)), 0, by norm_num⟩
  | 2 => ⟨((267256032355/281474976710656), (-41862493553/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-331765363399/4503599627370496), (69731456213/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((205346612599/36028797018963968), (-27198938293/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((-126735027995/288230376151711744), (81403442393/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((311946358337/9223372036854775808), (-29581022049/2305843009213693952)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-191368199677/73786976294838206464), (84162754905/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((234044456747/1180591620717411303424), (-117748457773/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-285276490677/18889465931478580854784), (81275500193/9444732965739290427392)), (11/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((173244345133/151115727451828646838272), (-55486732841/75557863725914323419136)), (1/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-209622335571/2417851639229258349412352), (75063635817/1208925819614629174706176)), (3/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((126305299667/19342813113834066795298816), (-201489895227/38685626227668133590597632)), (17/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (423/1280)))⁻¹=value ((3481600/22254843), (-60160/7418281)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/22254843), (-60160/7418281))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((256354045785/562949953421312), (-99544458783/281474976710656)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-222949761809/562949953421312), (232353356965/562949953421312)), (7/562949953421312), by norm_num⟩
  | 2 => ⟨((221916712373/1125899906842624), (-160015450123/562949953421312)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-79061184819/1125899906842624), (340297886563/2251799813685248)), (11/2251799813685248), by norm_num⟩
  | 4 => ⟨((79297577867/4503599627370496), (-308986567675/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((-28201067743/18014398509481984), (251474440813/9007199254740992)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-28265800867/18014398509481984), (-188055236169/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 7 => ⟨((99154291967/72057594037927936), (261289734839/72057594037927936)), (7/36028797018963968), by norm_num⟩
  | 8 => ⟨((-13897874167/18014398509481984), (-21085521705/18014398509481984)), (13/144115188075855872), by norm_num⟩
  | 9 => ⟨((209084549361/576460752303423488), (12495468087/36028797018963968)), (11/288230376151711744), by norm_num⟩
  | 10 => ⟨((-177244661615/1152921504606846976), (-52450130943/576460752303423488)), (19/1152921504606846976), by norm_num⟩
  | 11 => ⟨((279001170419/4611686018427387904), (43652556829/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 12 => ⟨((-51649852747/2305843009213693952), (-29151926515/18446744073709551616)), (53/18446744073709551616), by norm_num⟩
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
  | 0 => ⟨((59/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/89292529), (-541440/89292529)), 0, by norm_num⟩
  | 1 => ⟨((-72855282483200/7973155735215841), (6542327808000/7973155735215841)), 0, by norm_num⟩
  | 2 => ⟨((346646148497/562949953421312), (-23424977511/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-372996786943/9007199254740992), (67534023337/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((200259941317/72057594037927936), (-11400533757/18014398509481984)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((-214583695165/1152921504606846976), (29541036321/576460752303423488)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((229436288719/18446744073709551616), (-37184956249/9223372036854775808)), (3/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-61193422317/73786976294838206464), (91640590523/295147905179352825856)), (1/73786976294838206464), by norm_num⟩
  | 8 => ⟨((260539742207/4722366482869645213696), (-111081351473/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-138332286505/37778931862957161709568), (66446088637/37778931862957161709568)), (7/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((146531418239/604462909807314587353088), (-157286173211/1208925819614629174706176)), (9/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-4837996917/302231454903657293676544), (92244950541/9671406556917033397649408)), (11/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((326249268733/309485009821345068724781056), (-6710738969/9671406556917033397649408)), (13/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (423/1280)))⁻¹=value ((12083200/89292529), (-541440/89292529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/89292529), (-541440/89292529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((267864067553/4503599627370496), (-227963666997/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 1 => ⟨((-123760312069/2251799813685248), (278590714641/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 2 => ⟨((64130485529/2251799813685248), (-198210874723/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((-93490206621/9007199254740992), (26954203605/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((93544027975/36028797018963968), (-198920215395/18014398509481984)), (15/36028797018963968), by norm_num⟩
  | 5 => ⟨((-13312138053/72057594037927936), (327326807175/72057594037927936)), (13/72057594037927936), by norm_num⟩
  | 6 => ⟨((-39905580643/144115188075855872), (-7705852327/4503599627370496)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((133807269471/576460752303423488), (344308244957/576460752303423488)), (5/144115188075855872), by norm_num⟩
  | 8 => ⟨((-74370566249/576460752303423488), (-111500158505/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 9 => ⟨((279007593359/4611686018427387904), (264843018107/4611686018427387904)), (31/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-14770650843/576460752303423488), (-139111226693/9223372036854775808)), (27/9223372036854775808), by norm_num⟩
  | 11 => ⟨((371922218205/36893488147419103232), (57881674041/18446744073709551616)), (45/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-68849213447/18446744073709551616), (-4791898309/18446744073709551616)), (37/73786976294838206464), by norm_num⟩
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
  | 0 => ⟨((67/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/115097329), (-541440/115097329)), 0, by norm_num⟩
  | 1 => ⟨((-93994574643200/13247395142934241), (7429423104000/13247395142934241)), 0, by norm_num⟩
  | 2 => ⟨((474706268769/1125899906842624), (-28214327513/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-450622224713/18014398509481984), (71683081019/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((213539128479/144115188075855872), (-85325452643/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-404110048295/4611686018427387904), (97450670289/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((190874029675/36893488147419103232), (-108150587021/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-90004471213/295147905179352825856), (117513953021/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 8 => ⟨((338940595507/18889465931478580854784), (-125626376011/18889465931478580854784)), (7/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-39816633193/37778931862957161709568), (132570296369/302231454903657293676544)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((9337758939/151115727451828646838272), (-138424975729/4835703278458516698824704)), (9/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-69943916057/19342813113834066795298816), (143266497895/77371252455336267181195264)), (5/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((261441308801/1237940039285380274899124224), (-9197986311/77371252455336267181195264)), (11/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (423/1280)))⁻¹=value ((13721600/115097329), (-541440/115097329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/115097329), (-541440/115097329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((30861662667/4503599627370496), (-227498490347/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 1 => ⟨((-119883789343/18014398509481984), (289159481113/36028797018963968)), (5/18014398509481984), by norm_num⟩
  | 2 => ⟨((16060024843/4503599627370496), (-211668707943/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-47685765007/36028797018963968), (235015528235/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 4 => ⟨((94773202327/288230376151711744), (-439889442925/288230376151711744)), (9/144115188075855872), by norm_num⟩
  | 5 => ⟨((-9607123805/576460752303423488), (365573582629/576460752303423488)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((-47913849369/1152921504606846976), (-277305999813/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((154608063507/4611686018427387904), (48626639191/576460752303423488)), (25/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-170514453789/9223372036854775808), (-63184058245/2305843009213693952)), (21/9223372036854775808), by norm_num⟩
  | 9 => ⟨((159550891247/18446744073709551616), (150373936933/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-270090005493/73786976294838206464), (-79067545129/36893488147419103232)), (1/2305843009213693952), by norm_num⟩
  | 11 => ⟨((212479952065/147573952589676412928), (8223440275/18446744073709551616)), (27/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-314659590211/590295810358705651712), (-10801828587/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
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
  | 0 => ⟨((75/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/48059643), (-60160/16019881)), 0, by norm_num⟩
  | 1 => ⟨((-13090913484800/2309729285287449), (308019200000/769909761762483)), 0, by norm_num⟩
  | 2 => ⟨((339067461225/1125899906842624), (-35975638697/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-71974422207/4503599627370496), (40847605219/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((244140638499/288230376151711744), (-43462580627/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-413538133877/9223372036854775808), (88753356823/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 6 => ⟨((174890773917/73786976294838206464), (-88065997383/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-36933012043/295147905179352825856), (5347797531/147573952589676412928)), (3/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((124622935323/18889465931478580854784), (-40900589615/18889465931478580854784)), (3/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-52492082843/151115727451828646838272), (4825316039/37778931862957161709568)), (3/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((353262345459/19342813113834066795298816), (-36053948579/4835703278458516698824704)), (3/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-296743800979/309485009821345068724781056), (33381090867/77371252455336267181195264)), (3/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((248895695525/4951760157141521099596496896), (-122714363427/4951760157141521099596496896)), (3/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (423/1280)))⁻¹=value ((5120000/48059643), (-60160/16019881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/48059643), (-60160/16019881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12724135043/18014398509481984), (-50327114315/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 1 => ⟨((-51531773207/72057594037927936), (264751854959/288230376151711744)), (5/144115188075855872), by norm_num⟩
  | 2 => ⟨((28405992027/72057594037927936), (-99374653959/144115188075855872)), (9/288230376151711744), by norm_num⟩
  | 3 => ⟨((-42790345849/288230376151711744), (112381614827/288230376151711744)), (11/576460752303423488), by norm_num⟩
  | 4 => ⟨((84103748787/2305843009213693952), (-426286470767/2305843009213693952)), (19/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-2282091869/2305843009213693952), (178793784101/2305843009213693952)), (17/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-25011687545/4611686018427387904), (-273013803143/9223372036854775808)), (15/9223372036854775808), by norm_num⟩
  | 7 => ⟨((78082200885/18446744073709551616), (384696006385/36893488147419103232)), (13/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-85499744371/36893488147419103232), (-125337380423/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 9 => ⟨((79828720053/73786976294838206464), (149429809243/147573952589676412928)), (5/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-4220029385/9223372036854775808), (-157299916699/590295810358705651712)), (17/295147905179352825856), by norm_num⟩
  | 11 => ⟨((212431336839/1180591620717411303424), (4089321173/73786976294838206464)), (29/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-9830599469/147573952589676412928), (-10652210429/2361183241434822606848)), (23/2361183241434822606848), by norm_num⟩
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
  | 0 => ⟨((83/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/176537329), (-541440/176537329)), 0, by norm_num⟩
  | 1 => ⟨((-144326222643200/31165428530454241), (9203613696000/31165428530454241)), 0, by norm_num⟩
  | 2 => ⟨((31314133193/140737488355328), (-6000824527/281474976710656)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-384763945091/36028797018963968), (49272793225/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((4612121711/9007199254740992), (-11848884819/144115188075855872)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((-452423684241/18446744073709551616), (87502700513/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((21647266715/18446744073709551616), (-78504243553/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-264873024733/4722366482869645213696), (68970236705/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((404680361163/151115727451828646838272), (-119253783169/151115727451828646838272)), (11/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-308800407095/2417851639229258349412352), (101790761435/2417851639229258349412352)), (5/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((117686141045/19342813113834066795298816), (-5374152261/2417851639229258349412352)), (9/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-358396332495/1237940039285380274899124224), (144021375115/1237940039285380274899124224)), (15/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((136269996131/9903520314283042199192993792), (-119733682071/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (423/1280)))⁻¹=value ((16998400/176537329), (-541440/176537329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/176537329), (-541440/176537329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37970921637/576460752303423488), (-160063659771/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 1 => ⟨((-39837786429/576460752303423488), (216935637927/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 2 => ⟨((179974934541/4611686018427387904), (-166573525603/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 3 => ⟨((-137124150185/9223372036854775808), (47887638219/1152921504606846976)), (5/2305843009213693952), by norm_num⟩
  | 4 => ⟨((16588601815/4611686018427387904), (-367741776377/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-3293991/36893488147419103232), (311175268487/36893488147419103232)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-2886616903/4611686018427387904), (-239038333181/73786976294838206464)), (7/36893488147419103232), by norm_num⟩
  | 7 => ⟨((140093315973/295147905179352825856), (169125217081/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-152398640589/590295810358705651712), (-110519784707/295147905179352825856)), (21/590295810358705651712), by norm_num⟩
  | 9 => ⟨((35500762509/295147905179352825856), (264009729719/2361183241434822606848)), (37/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-240060396369/4722366482869645213696), (-139091720887/4722366482869645213696)), (31/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((377566636631/18889465931478580854784), (57844611451/9444732965739290427392)), (53/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-279553851693/37778931862957161709568), (-2334226239/4722366482869645213696)), (43/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((91/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/212172529), (-541440/212172529)), 0, by norm_num⟩
  | 1 => ⟨((-173518578483200/45017182062255841), (10090708992000/45017182062255841)), 0, by norm_num⟩
  | 2 => ⟨((190276563477/1125899906842624), (-33242555801/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-33342175353/4503599627370496), (7782171923/9007199254740992)), (1/36028797018963968), by norm_num⟩
  | 4 => ⟨((186801838509/576460752303423488), (-13659853697/288230376151711744)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((-261417180661/18446744073709551616), (11505615983/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((45689810387/73786976294838206464), (-75354009593/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-127656397795/4722366482869645213696), (30206812183/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((356351742865/302231454903657293676544), (-47665103511/151115727451828646838272)), (7/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-248463478479/4835703278458516698824704), (74263830447/4835703278458516698824704)), (3/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((173080078519/77371252455336267181195264), (-114515727609/154742504910672534362390528)), (5/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-60227535103/618970019642690137449562112), (87537502755/2475880078570760549798248448)), (1/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((335002675061/79228162514264337593543950336), (-132862238185/79228162514264337593543950336)), (3/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (423/1280)))⁻¹=value ((18636800/212172529), (-541440/212172529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/212172529), (-541440/212172529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((206923000593/36893488147419103232), (-57789014103/9223372036854775808)), (5/18446744073709551616), by norm_num⟩
  | 1 => ⟨((-223888633255/36893488147419103232), (321805400599/36893488147419103232)), (7/18446744073709551616), by norm_num⟩
  | 2 => ⟨((64545081723/18446744073709551616), (-252196868123/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-99232030559/73786976294838206464), (147243903263/36893488147419103232)), (17/73786976294838206464), by norm_num⟩
  | 4 => ⟨((5885605075/18446744073709551616), (-285888535029/147573952589676412928)), (1/9223372036854775808), by norm_num⟩
  | 5 => ⟨((5888146947/590295810358705651712), (121948033347/147573952589676412928)), (13/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-76431922615/1180591620717411303424), (-376892052955/1180591620717411303424)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((113024897291/2361183241434822606848), (267740160855/2361183241434822606848)), (5/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-61107366151/2361183241434822606848), (-10965211903/295147905179352825856)), (9/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((113663747901/9444732965739290427392), (209919998705/18889465931478580854784)), (31/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-192034546985/37778931862957161709568), (-110698228493/37778931862957161709568)), (13/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((301980060385/151115727451828646838272), (92054089417/151115727451828646838272)), (11/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-223584946393/302231454903657293676544), (-29460524125/604462909807314587353088)), (71/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((99/8), (423/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/27898281), (-60160/27898281)), 0, by norm_num⟩
  | 1 => ⟨((-845248102400/259438027584987), (135528448000/778314082754961)), 0, by norm_num⟩
  | 2 => ⟨((295784384851/2251799813685248), (-23741522337/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-11916769571/2251799813685248), (20439765479/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 4 => ⟨((245639747935/1152921504606846976), (-32986869343/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((-79057592701/9223372036854775808), (51094477967/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((406809257131/1180591620717411303424), (-76925203569/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-130736667857/9444732965739290427392), (14177987777/4722366482869645213696)), (5/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((335868917353/604462909807314587353088), (-82293769617/604462909807314587353088)), (7/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-431105961737/19342813113834066795298816), (58956257057/9671406556917033397649408)), (5/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((69115505271/77371252455336267181195264), (-83609064359/309485009821345068724781056)), (1/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-354306400333/9903520314283042199192993792), (117562199837/9903520314283042199192993792)), (3/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((226855243655/158456325028528675187087900672), (-82057872121/158456325028528675187087900672)), (9/158456325028528675187087900672), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (423/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (423/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (423/1280)))⁻¹=value ((2252800/27898281), (-60160/27898281)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/27898281), (-60160/27898281))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16210668585/36893488147419103232), (-152897406575/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-144152624441/295147905179352825856), (218063017833/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 2 => ⟨((169254258611/590295810358705651712), (-174106915195/295147905179352825856)), (19/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-8185280219/73786976294838206464), (412387749815/1180591620717411303424)), (25/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((30328147021/1180591620717411303424), (-50572215353/295147905179352825856)), (3/295147905179352825856), by norm_num⟩
  | 5 => ⟨((1024149275/590295810358705651712), (347814722851/4722366482869645213696)), (5/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-7161101839/1180591620717411303424), (-270223756243/9444732965739290427392)), (19/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((82842193629/18889465931478580854784), (192708548437/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-44541461649/18889465931478580854784), (-253222876721/75557863725914323419136)), (27/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((165408874647/151115727451828646838272), (75875571811/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-279297690391/604462909807314587353088), (-160191901779/604462909807314587353088)), (5/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((219567227607/1208925819614629174706176), (4161941969/75557863725914323419136)), (17/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-162564635707/2417851639229258349412352), (-21124951281/4835703278458516698824704)), (27/2417851639229258349412352), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((230874834417/274877906944), (-657957759/34359738368)), (893/549755813888), by norm_num⟩
  | 1 => ⟨((-23620840849/2199023255552), (311068955393/2199023255552)), (2331/549755813888), by norm_num⟩
  | 2 => ⟨((384827767545/4398046511104), (-81869266413/2199023255552)), (25107/4398046511104), by norm_num⟩
  | 3 => ⟨((-79636110189/8796093022208), (232644802401/8796093022208)), (5813/1099511627776), by norm_num⟩
  | 4 => ⟨((165285347143/35184372088832), (-162176726713/17592186044416)), (133173/35184372088832), by norm_num⟩
  | 5 => ⟨((-6301034925/17592186044416), (269054308079/70368744177664)), (157431/70368744177664), by norm_num⟩
  | 6 => ⟨((-31273758023/281474976710656), (-376925808951/281474976710656)), (162449/140737488355328), by norm_num⟩
  | 7 => ⟨((22088558055/140737488355328), (258545767343/562949953421312)), (153513/281474976710656), by norm_num⟩
  | 8 => ⟨((-102241318887/1125899906842624), (-327685275973/2251799813685248)), (34333/140737488355328), by norm_num⟩
  | 9 => ⟨((12204475233/281474976710656), (24083963431/562949953421312)), (236247/2251799813685248), by norm_num⟩
  | 10 => ⟨((-332174917631/18014398509481984), (-25140411803/2251799813685248)), (783349/18014398509481984), by norm_num⟩
  | 11 => ⟨((32720871547/4503599627370496), (83728456095/36028797018963968)), (624077/36028797018963968), by norm_num⟩
  | 12 => ⟨((-193874399361/72057594037927936), (-902245995/4503599627370496)), (476305/72057594037927936), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((230874834417/274877906944), (-657957759/34359738368)), (447/274877906944), by norm_num⟩
  | 1 => ⟨((-23620840849/2199023255552), (311068955393/2199023255552)), (9325/2199023255552), by norm_num⟩
  | 2 => ⟨((384827767545/4398046511104), (-81869266413/2199023255552)), (6277/1099511627776), by norm_num⟩
  | 3 => ⟨((-79636110189/8796093022208), (232644802401/8796093022208)), (46505/8796093022208), by norm_num⟩
  | 4 => ⟨((165285347143/35184372088832), (-162176726713/17592186044416)), (133175/35184372088832), by norm_num⟩
  | 5 => ⟨((-6301034925/17592186044416), (269054308079/70368744177664)), (78717/35184372088832), by norm_num⟩
  | 6 => ⟨((-31273758023/281474976710656), (-376925808951/281474976710656)), (162455/140737488355328), by norm_num⟩
  | 7 => ⟨((22088558055/140737488355328), (258545767343/562949953421312)), (307049/562949953421312), by norm_num⟩
  | 8 => ⟨((-102241318887/1125899906842624), (-327685275973/2251799813685248)), (549419/2251799813685248), by norm_num⟩
  | 9 => ⟨((12204475233/281474976710656), (24083963431/562949953421312)), (472675/4503599627370496), by norm_num⟩
  | 10 => ⟨((-332174917631/18014398509481984), (-25140411803/2251799813685248)), (392035/9007199254740992), by norm_num⟩
  | 11 => ⟨((32720871547/4503599627370496), (83728456095/36028797018963968)), (625519/36028797018963968), by norm_num⟩
  | 12 => ⟨((-193874399361/72057594037927936), (-902245995/4503599627370496)), (958375/144115188075855872), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile001Gamma
