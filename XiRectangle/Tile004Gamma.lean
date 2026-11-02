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
namespace Reinmann.XiRectangle.Tile004Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1269/640))
  have he : value ((3/4), (1269/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/294704761), (-1624320/294704761)), 0, by norm_num⟩
  | 1 => ⟨((-238783724748800/86850896156067121), (35594698752000/86850896156067121)), 0, by norm_num⟩
  | 2 => ⟨((28453873311/281474976710656), (-12843178833/562949953421312)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-33285981807/9007199254740992), (5074592937/4503599627370496)), (1/36028797018963968), by norm_num⟩
  | 4 => ⟨((154824545169/1152921504606846976), (-60040517209/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-44725957313/9223372036854775808), (170170414925/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 6 => ⟨((205342938373/1180591620717411303424), (-117004978833/1180591620717411303424)), (1/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-58495824397/9444732965739290427392), (78656155699/18889465931478580854784)), (3/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((66125716325/302231454903657293676544), (-103896328081/604462909807314587353088)), (9/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-74090261769/9671406556917033397649408), (16908863051/2417851639229258349412352)), (7/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((41091232797/154742504910672534362390528), (-174002758175/618970019642690137449562112)), (5/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-90102139773/9903520314283042199192993792), (27688782989/2475880078570760549798248448)), (7/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((24357400513/79228162514264337593543950336), (-139713975903/316912650057057350374175801344)), (19/633825300114114700748351602688), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (1269/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (1269/1280)))⁻¹=value ((21913600/294704761), (-1624320/294704761)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/294704761), (-1624320/294704761))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44601121293/17179869184), (10168905259/137438953472)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((10956800/294704761), (-812160/294704761)), 0, by norm_num⟩
  | 2 => ⟨((-59695931187200/86850896156067121), (8898674688000/86850896156067121)), 0, by norm_num⟩
  | 3 => ⟨((9484624437/562949953421312), (-4281059611/1125899906842624)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-33285981807/72057594037927936), (5074592937/36028797018963968)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((123859636135/9223372036854775808), (-48032413767/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-238538439003/590295810358705651712), (113446943283/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 7 => ⟨((234677643855/18889465931478580854784), (-133719975809/18889465931478580854784)), (5/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-58495824397/151115727451828646838272), (78656155699/302231454903657293676544)), (3/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((58778414511/4835703278458516698824704), (-184704583255/19342813113834066795298816)), (9/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-237088837661/618970019642690137449562112), (216433447053/618970019642690137449562112)), (3/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((119538131773/9903520314283042199192993792), (-126547460491/9903520314283042199192993792)), (15/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-30034046591/79228162514264337593543950336), (295347018549/633825300114114700748351602688)), (19/633825300114114700748351602688), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (27/20480)), 0, by norm_num⟩
  | 45 => ⟨((107238362153/4080638361600), (-53649/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-51572977113919/1915179604377600), (379398491259/197568495616000)), 0, by norm_num⟩
  | 43 => ⟨((484748932927/17592186044416), (-34896306435/17592186044416)), (1/17592186044416), by norm_num⟩
  | 42 => ⟨((-124057104569/4398046511104), (17880810193/8796093022208)), (1/17592186044416), by norm_num⟩
  | 41 => ⟨((508274289901/17592186044416), (-36614888051/17592186044416)), (1/17592186044416), by norm_num⟩
  | 40 => ⟨((-260462318747/8796093022208), (585957411/274877906944)), (1/8796093022208), by norm_num⟩
  | 39 => ⟨((133555551107/4398046511104), (-1200954661/549755813888)), (1/8796093022208), by norm_num⟩
  | 38 => ⟨((-274108413413/8796093022208), (4925870499/2199023255552)), (1/4398046511104), by norm_num⟩
  | 37 => ⟨((281482270719/8796093022208), (-20217152155/8796093022208)), (1/8796093022208), by norm_num⟩
  | 36 => ⟨((-18078993071/549755813888), (20758331679/8796093022208)), (1/8796093022208), by norm_num⟩
  | 35 => ⟨((74372013517/2199023255552), (-21329290515/8796093022208)), (1/8796093022208), by norm_num⟩
  | 34 => ⟨((-306193627675/8796093022208), (10966278241/4398046511104)), (1/4398046511104), by norm_num⟩
  | 33 => ⟨((157712080421/4398046511104), (-11285476155/4398046511104)), (1/4398046511104), by norm_num⟩
  | 32 => ⟨((-325228621883/8796093022208), (11623819821/4398046511104)), (1/8796093022208), by norm_num⟩
  | 31 => ⟨((167831133013/4398046511104), (-23966171405/8796093022208)), (1/4398046511104), by norm_num⟩
  | 30 => ⟨((-346787678003/8796093022208), (24730554273/8796093022208)), (1/8796093022208), by norm_num⟩
  | 29 => ⟨((358676029283/8796093022208), (-25545323523/8796093022208)), (1/8796093022208), by norm_num⟩
  | 28 => ⟨((-371408603331/8796093022208), (26415633213/8796093022208)), (1/8796093022208), by norm_num⟩
  | 27 => ⟨((385078658037/8796093022208), (-27347365489/8796093022208)), (1/8796093022208), by norm_num⟩
  | 26 => ⟨((-199896857801/4398046511104), (28347263921/8796093022208)), (1/4398046511104), by norm_num⟩
  | 25 => ⟨((103919599735/2199023255552), (-29423097259/8796093022208)), (1/4398046511104), by norm_num⟩
  | 24 => ⟨((-216438986547/4398046511104), (30583862063/8796093022208)), (1/8796093022208), by norm_num⟩
  | 23 => ⟨((451562805013/8796093022208), (-31840035371/8796093022208)), (1/4398046511104), by norm_num⟩
  | 22 => ⟨((-471934032169/8796093022208), (8300973125/2199023255552)), (1/4398046511104), by norm_num⟩
  | 21 => ⟨((15444713765/274877906944), (-34689910431/8796093022208)), (1/4398046511104), by norm_num⟩
  | 20 => ⟨((-259369955625/4398046511104), (18157642471/4398046511104)), (1/4398046511104), by norm_num⟩
  | 19 => ⟨((136451957747/2199023255552), (-9525150205/2199023255552)), (1/4398046511104), by norm_num⟩
  | 18 => ⟨((-287928804239/4398046511104), (10017677689/2199023255552)), (1/4398046511104), by norm_num⟩
  | 17 => ⟨((76176372303/1099511627776), (-21127951497/4398046511104)), (1/4398046511104), by norm_num⟩
  | 16 => ⟨((-20222468895/274877906944), (22346737443/4398046511104)), (1/4398046511104), by norm_num⟩
  | 15 => ⟨((172451206571/2199023255552), (-23714943665/4398046511104)), (1/4398046511104), by norm_num⟩
  | 14 => ⟨((-92315571265/1099511627776), (25261883447/4398046511104)), (1/4398046511104), by norm_num⟩
  | 13 => ⟨((397328064407/4398046511104), (-13512543167/2199023255552)), (1/4398046511104), by norm_num⟩
  | 12 => ⟨((-430015959023/4398046511104), (907918707/137438953472)), (1/4398046511104), by norm_num⟩
  | 11 => ⟨((14642864713/137438953472), (-3926450631/549755813888)), (1/4398046511104), by norm_num⟩
  | 10 => ⟨((-257366668503/2199023255552), (17093760821/2199023255552)), (1/4398046511104), by norm_num⟩
  | 9 => ⟨((285500957503/2199023255552), (-9375813933/1099511627776)), (1/2199023255552), by norm_num⟩
  | 8 => ⟨((-160278001359/1099511627776), (10383451775/1099511627776)), (1/2199023255552), by norm_num⟩
  | 7 => ⟨((365450621187/2199023255552), (-23269646649/2199023255552)), (1/2199023255552), by norm_num⟩
  | 6 => ⟨((-212509381947/1099511627776), (26462053273/2199023255552)), (1/2199023255552), by norm_num⟩
  | 5 => ⟨((507894626749/2199023255552), (-7669205449/549755813888)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((-39448840721/137438953472), (18251767641/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((208574773545/549755813888), (-5637336063/274877906944)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((-308398594453/549755813888), (1846705847/68719476736)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((37464815027/34359738368), (-10766534901/274877906944)), (1/274877906944), by norm_num⟩
  | 0 => ⟨((-97010888197/549755813888), (81351242075/1099511627776)), (1/549755813888), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (1269/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (1269/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (1269/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((44601121293/17179869184), (10168905259/137438953472)), (1/137438953472), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (1269/1280))) (z:=((-21/128), (1269/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((44601121293/17179869184), (10168905259/137438953472))) (r:=(1/137438953472)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((286489623559/8589934592), (15145853077/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((489138094167/274877906944), (2636916353/68719476736)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((837103246924800/86850896156067121), (-64286192017440/86850896156067121)), 0, by norm_num⟩
  | 3 => ⟨((-276927221819/2251799813685248), (42734000017/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((168396981895/72057594037927936), (-39323069825/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-243995192599/4611686018427387904), (19240723259/1152921504606846976)), (23/4611686018427387904), by norm_num⟩
  | 6 => ⟨((389926972771/295147905179352825856), (-78224086267/147573952589676412928)), (15/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-10352649057/295147905179352825856), (40770910855/2361183241434822606848)), (67/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((9161670883/9444732965739290427392), (-43262013415/75557863725914323419136)), (83/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-66690891981/2417851639229258349412352), (186009311503/9671406556917033397649408)), (7/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((247363135851/309485009821345068724781056), (-201872028367/309485009821345068724781056)), (157/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-116098655729/4951760157141521099596496896), (220679873555/9903520314283042199192993792)), (201/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((219452268877/316912650057057350374175801344), (-242566701959/316912650057057350374175801344)), (253/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((171599248391/8589934592), (43551182625/17179869184)), (5/17179869184), by norm_num⟩
  | 1 => ⟨((351699140695/274877906944), (2636916353/68719476736)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((837103246924800/86850896156067121), (-64286192017440/86850896156067121)), 0, by norm_num⟩
  | 3 => ⟨((-276927221819/2251799813685248), (42734000017/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((168396981895/72057594037927936), (-39323069825/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-243995192599/4611686018427387904), (19240723259/1152921504606846976)), (23/4611686018427387904), by norm_num⟩
  | 6 => ⟨((389926972771/295147905179352825856), (-78224086267/147573952589676412928)), (15/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-10352649057/295147905179352825856), (40770910855/2361183241434822606848)), (67/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((9161670883/9444732965739290427392), (-43262013415/75557863725914323419136)), (83/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-66690891981/2417851639229258349412352), (186009311503/9671406556917033397649408)), (7/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((247363135851/309485009821345068724781056), (-201872028367/309485009821345068724781056)), (157/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-116098655729/4951760157141521099596496896), (220679873555/9903520314283042199192993792)), (201/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((219452268877/316912650057057350374175801344), (-242566701959/316912650057057350374175801344)), (253/316912650057057350374175801344), by norm_num⟩
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
  | 0 => ⟨((358985740571/17179869184), (43551182625/17179869184)), (3/8589934592), by norm_num⟩
  | 1 => ⟨((351699140695/274877906944), (2636916353/68719476736)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((837103246924800/86850896156067121), (-64286192017440/86850896156067121)), 0, by norm_num⟩
  | 3 => ⟨((-276927221819/2251799813685248), (42734000017/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((168396981895/72057594037927936), (-39323069825/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-243995192599/4611686018427387904), (19240723259/1152921504606846976)), (23/4611686018427387904), by norm_num⟩
  | 6 => ⟨((389926972771/295147905179352825856), (-78224086267/147573952589676412928)), (15/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-10352649057/295147905179352825856), (40770910855/2361183241434822606848)), (67/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((9161670883/9444732965739290427392), (-43262013415/75557863725914323419136)), (83/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-66690891981/2417851639229258349412352), (186009311503/9671406556917033397649408)), (7/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((247363135851/309485009821345068724781056), (-201872028367/309485009821345068724781056)), (157/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-116098655729/4951760157141521099596496896), (220679873555/9903520314283042199192993792)), (201/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((219452268877/316912650057057350374175801344), (-242566701959/316912650057057350374175801344)), (253/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((477567449497600/86850896156067121), (-71189397504000/86850896156067121)), 0, by norm_num⟩
  | 1 => ⟨((-28453873311/70368744177664), (12843178833/140737488355328)), (1/562949953421312), by norm_num⟩
  | 2 => ⟨((99857945421/4503599627370496), (-15223778811/2251799813685248)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((-154824545169/144115188075855872), (60040517209/144115188075855872)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((223629786565/4611686018427387904), (-6647281833/288230376151711744)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-308014407559/147573952589676412928), (87753734125/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 6 => ⟨((102367692695/1180591620717411303424), (-68824136237/1180591620717411303424)), (5/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-66125716325/18889465931478580854784), (207792656163/75557863725914323419136)), (1/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((166703088981/1208925819614629174706176), (-38044941865/302231454903657293676544)), (7/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-205456163985/38685626227668133590597632), (217503447719/38685626227668133590597632)), (11/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((30972610547/154742504910672534362390528), (-152288306439/618970019642690137449562112)), (9/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-73072201539/9903520314283042199192993792), (209570963855/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((168339395023/633825300114114700748351602688), (-284071484249/633825300114114700748351602688)), (9/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((28453873311/70368744177664), (-12843178833/140737488355328)), (1/562949953421312), by norm_num⟩
  | 1 => ⟨((-99857945421/2251799813685248), (15223778811/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((232236817753/72057594037927936), (-90060775813/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((-223629786565/1152921504606846976), (6647281833/72057594037927936)), (3/1152921504606846976), by norm_num⟩
  | 4 => ⟨((48127251181/4611686018427387904), (-13711520957/2305843009213693952)), (1/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-76775769521/147573952589676412928), (206472408711/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 6 => ⟨((115720003569/4722366482869645213696), (-181818574143/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-166703088981/151115727451828646838272), (38044941865/37778931862957161709568)), (3/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((57784546121/1208925819614629174706176), (-244691378685/4835703278458516698824704)), (11/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-154863052735/77371252455336267181195264), (95180191525/38685626227668133590597632)), (9/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((200948554233/2475880078570760549798248448), (-288160075301/2475880078570760549798248448)), (1/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-126254546267/39614081257132168796771975168), (213053613187/39614081257132168796771975168)), (13/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((76661449709/633825300114114700748351602688), (-77177683369/316912650057057350374175801344)), (5/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((33285981807/1125899906842624), (-5074592937/562949953421312)), (1/4503599627370496), by norm_num⟩
  | 1 => ⟨((-154824545169/36028797018963968), (60040517209/36028797018963968)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((55907446641/144115188075855872), (-6647281833/36028797018963968)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-128339336483/4611686018427387904), (146256223541/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((255919231737/147573952589676412928), (-10753771287/9223372036854775808)), (3/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-231440007137/2361183241434822606848), (90909287071/1180591620717411303424)), (7/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((24310867143/4722366482869645213696), (-177543062037/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-154092122989/604462909807314587353088), (81563792895/302231454903657293676544)), (7/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((232294579103/19342813113834066795298816), (-285540574575/19342813113834066795298816)), (13/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-167457128527/309485009821345068724781056), (60033349021/77371252455336267181195264)), (3/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((57866667039/2475880078570760549798248448), (-97649572711/2475880078570760549798248448)), (11/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-153322899417/158456325028528675187087900672), (77177683369/39614081257132168796771975168)), (19/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((24248095453/633825300114114700748351602688), (-59500302585/633825300114114700748351602688)), (1/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((154824545169/72057594037927936), (-60040517209/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 1 => ⟨((-223629786565/576460752303423488), (6647281833/36028797018963968)), (3/576460752303423488), by norm_num⟩
  | 2 => ⟨((48127251181/1152921504606846976), (-13711520957/576460752303423488)), (1/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-255919231737/73786976294838206464), (10753771287/4611686018427387904)), (3/36893488147419103232), by norm_num⟩
  | 4 => ⟨((144650004461/590295810358705651712), (-113636608839/590295810358705651712)), (9/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-72932601429/4722366482869645213696), (133157296527/9444732965739290427392)), (5/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((134830607615/151115727451828646838272), (-71368318783/75557863725914323419136)), (3/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-116147289551/2417851639229258349412352), (285540574575/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((188389269593/77371252455336267181195264), (-270150070595/77371252455336267181195264)), (13/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-144666667597/1237940039285380274899124224), (244123931777/1237940039285380274899124224)), (13/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((105409493349/19807040628566084398385987584), (-212238629265/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-72744286359/316912650057057350374175801344), (178500907755/316912650057057350374175801344)), (23/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((23601412155/2535301200456458802993406410752), (-145854718337/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44725957313/288230376151711744), (-170170414925/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-308014407559/9223372036854775808), (87753734125/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 2 => ⟨((76775769521/18446744073709551616), (-103236204355/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-231440007137/590295810358705651712), (90909287071/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 4 => ⟨((72932601429/2361183241434822606848), (-133157296527/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-80898364569/37778931862957161709568), (171283965079/75557863725914323419136)), (7/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((40651551343/302231454903657293676544), (-99939201101/604462909807314587353088)), (9/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-75355707837/9671406556917033397649408), (54030014119/4835703278458516698824704)), (11/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((130200000837/309485009821345068724781056), (-219711538599/309485009821345068724781056)), (3/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-105409493349/4951760157141521099596496896), (212238629265/4951760157141521099596496896)), (3/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((80018714995/79228162514264337593543950336), (-98175499265/39614081257132168796771975168)), (13/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-113286778343/2535301200456458802993406410752), (350051324009/2535301200456458802993406410752)), (3/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((73603014619/40564819207303340847894502572032), (-302072435699/40564819207303340847894502572032)), (11/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((205342938373/18446744073709551616), (-117004978833/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-102367692695/36893488147419103232), (68824136237/36893488147419103232)), (5/73786976294838206464), by norm_num⟩
  | 2 => ⟨((231440007137/590295810358705651712), (-90909287071/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-24310867143/590295810358705651712), (44385765509/1180591620717411303424)), (7/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((134830607615/37778931862957161709568), (-71368318783/18889465931478580854784)), (7/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-162606205371/604462909807314587353088), (99939201101/302231454903657293676544)), (9/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((175829984953/9671406556917033397649408), (-7879377059/302231454903657293676544)), (3/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-173600001117/154742504910672534362390528), (73237179533/38685626227668133590597632)), (1/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((158114240023/2475880078570760549798248448), (-318357943897/2475880078570760549798248448)), (9/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-133364524991/39614081257132168796771975168), (327251664217/39614081257132168796771975168)), (5/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((51923106741/316912650057057350374175801344), (-320880380341/633825300114114700748351602688)), (11/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-36801507309/5070602400912917605986812821504), (302072435699/10141204801825835211973625643008)), (11/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((45696366163/162259276829213363391578010288128), (-274405449825/162259276829213363391578010288128)), (11/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((58495824397/73786976294838206464), (-78656155699/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-66125716325/295147905179352825856), (207792656163/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 2 => ⟨((41675772245/1180591620717411303424), (-38044941865/1180591620717411303424)), (7/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-154092122989/37778931862957161709568), (163127585789/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((116147289551/302231454903657293676544), (-142770287287/302231454903657293676544)), (7/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((-75355707837/2417851639229258349412352), (216120056475/4835703278458516698824704)), (11/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((43400000279/19342813113834066795298816), (-73237179533/19342813113834066795298816)), (15/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-90350994299/618970019642690137449562112), (45479706271/154742504910672534362390528)), (21/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((42867168747/4951760157141521099596496896), (-105188034927/4951760157141521099596496896)), (13/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-18543966693/39614081257132168796771975168), (28650033959/19807040628566084398385987584)), (15/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((57830940057/2535301200456458802993406410752), (-237342628049/2535301200456458802993406410752)), (17/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-19584156927/20282409603651670423947251286016), (117602335639/20282409603651670423947251286016)), (9/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((40941092253/1298074214633706907132624082305024), (-224265704441/649037107316853453566312041152512)), (19/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((66125716325/1180591620717411303424), (-103896328081/2361183241434822606848)), (9/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-166703088981/9444732965739290427392), (38044941865/2361183241434822606848)), (7/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((231138184483/75557863725914323419136), (-244691378685/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-116147289551/302231454903657293676544), (142770287287/302231454903657293676544)), (13/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((188389269593/4835703278458516698824704), (-135075035297/2417851639229258349412352)), (7/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-130200000837/38685626227668133590597632), (219711538599/38685626227668133590597632)), (13/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((158114240023/618970019642690137449562112), (-318357943897/618970019642690137449562112)), (9/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-42867168747/2475880078570760549798248448), (210376069853/4951760157141521099596496896)), (13/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((83447850119/79228162514264337593543950336), (-257850305631/79228162514264337593543950336)), (17/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((-72288675071/1267650600228229401496703205376), (296678285061/1267650600228229401496703205376)), (21/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((53856431549/20282409603651670423947251286016), (-323406423007/20282409603651670423947251286016)), (25/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-15352909595/162259276829213363391578010288128), (336398556661/324518553658426726783156020576256)), (7/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((357578591/324518553658426726783156020576256), (-335774667605/5192296858534827628530496329220096)), (15/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((74090261769/18889465931478580854784), (-16908863051/4722366482869645213696)), (7/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((-102728081993/75557863725914323419136), (27187930965/18889465931478580854784)), (11/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((154863052735/604462909807314587353088), (-95180191525/302231454903657293676544)), (5/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-167457128527/4835703278458516698824704), (60033349021/1208925819614629174706176)), (3/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((144666667597/38685626227668133590597632), (-1907218217/302231454903657293676544)), (7/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-105409493349/309485009821345068724781056), (212238629265/309485009821345068724781056)), (7/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((133364524991/4951760157141521099596496896), (-327251664217/4951760157141521099596496896)), (21/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((-18543966693/9903520314283042199192993792), (28650033959/4951760157141521099596496896)), (1/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((72288675071/633825300114114700748351602688), (-296678285061/633825300114114700748351602688)), (21/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((-59840479499/10141204801825835211973625643008), (44917558751/1267650600228229401496703205376)), (7/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((37529334565/162259276829213363391578010288128), (-205576895737/81129638414606681695789005144064)), (17/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((-7628343275/2596148429267413814265248164610048), (223849778403/1298074214633706907132624082305024)), (5/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((-26604932701/41538374868278621028243970633760768), (-58331004661/5192296858534827628530496329220096)), (45/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((41091232797/151115727451828646838272), (-174002758175/604462909807314587353088)), (5/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((-30972610547/302231454903657293676544), (19036038305/151115727451828646838272)), (9/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((25118569279/1208925819614629174706176), (-288160075301/9671406556917033397649408)), (17/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((-57866667039/19342813113834066795298816), (97649572711/19342813113834066795298816)), (11/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((105409493349/309485009821345068724781056), (-13264914329/19342813113834066795298816)), (13/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((-80018714995/2475880078570760549798248448), (98175499265/1237940039285380274899124224)), (7/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((103846213481/39614081257132168796771975168), (-320880380341/39614081257132168796771975168)), (23/39614081257132168796771975168), by norm_num⟩
  | 7 => ⟨((-57830940057/316912650057057350374175801344), (237342628049/316912650057057350374175801344)), (9/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((53856431549/5070602400912917605986812821504), (-323406423007/5070602400912917605986812821504)), (25/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-37529334565/81129638414606681695789005144064), (205576895737/40564819207303340847894502572032)), (35/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((4195588801/649037107316853453566312041152512), (-246234756243/649037107316853453566312041152512)), (11/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((3990739905/2596148429267413814265248164610048), (279988822373/10384593717069655257060992658440192)), (7/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((-40042655503/166153499473114484112975882535043072), (-304060126295/166153499473114484112975882535043072)), (33/166153499473114484112975882535043072), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/884114283), (-135360/294704761)), 0, by norm_num⟩
  | 1 => ⟨((-59695931187200/260552688468201363), (2966224896000/86850896156067121)), 0, by norm_num⟩
  | 2 => ⟨((9484624437/1125899906842624), (-4281059611/2251799813685248)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((-11095327269/36028797018963968), (1691530979/18014398509481984)), (3/1152921504606846976), by norm_num⟩
  | 4 => ⟨((51608181723/4611686018427387904), (-80054022945/18446744073709551616)), (3/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-238538439003/590295810358705651712), (113446943283/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 6 => ⟨((273790584497/18889465931478580854784), (-39001659611/4722366482869645213696)), (3/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-311977730117/604462909807314587353088), (209749748531/604462909807314587353088)), (9/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((176335243533/9671406556917033397649408), (-138528437441/9671406556917033397649408)), (7/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-24696753923/38685626227668133590597632), (180361205877/309485009821345068724781056)), (5/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((13697077599/618970019642690137449562112), (-232003677567/9903520314283042199192993792)), (7/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-30034046591/39614081257132168796771975168), (295347018549/316912650057057350374175801344)), (19/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((129906136069/5070602400912917605986812821504), (-46571325301/1267650600228229401496703205376)), (13/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359092195355/17179869184), (10885822947/4294967296)), (7/17179869184), by norm_num⟩
  | 1 => ⟨((175818081337/137438953472), (10557053337/274877906944)), (3/274877906944), by norm_num⟩
  | 2 => ⟨((339417272019/35184372088832), (-26110022949/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-277620679773/2251799813685248), (42945441389/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((338406719469/144115188075855872), (-9908945213/18014398509481984)), (17/144115188075855872), by norm_num⟩
  | 5 => ⟨((-122929387077/2305843009213693952), (2432787415/144115188075855872)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((197102475327/147573952589676412928), (-39721444065/73786976294838206464)), (31/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-336159421857/9444732965739290427392), (166360983241/9444732965739290427392)), (17/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((37335493077/37778931862957161709568), (-88688533665/151115727451828646838272)), (21/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-272937756405/9671406556917033397649408), (191645599187/9671406556917033397649408)), (113/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((127105837325/154742504910672534362390528), (-209122143291/309485009821345068724781056)), (79/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-119852911553/4951760157141521099596496896), (229909467885/9903520314283042199192993792)), (203/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((227571402381/316912650057057350374175801344), (-63552383321/79228162514264337593543950336)), (255/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-161870923725/144115188075855872), (73063417361/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 1 => ⟨((142020189043/1152921504606846976), (-86606386125/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-165146181513/18446744073709551616), (16010804589/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((79512813001/147573952589676412928), (-37815647761/147573952589676412928)), (5/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-17111911531/590295810358705651712), (39001659611/2361183241434822606848)), (7/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((109192205541/75557863725914323419136), (-36706205993/37778931862957161709568)), (3/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-164579560631/2417851639229258349412352), (129293208279/2417851639229258349412352)), (3/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((118544418831/38685626227668133590597632), (-108216723527/38685626227668133590597632)), (9/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-164364931189/1237940039285380274899124224), (5437586193/38685626227668133590597632)), (9/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((220249675001/39614081257132168796771975168), (-67683691751/9903520314283042199192993792)), (7/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((-142896749677/633825300114114700748351602688), (204913831325/633825300114114700748351602688)), (3/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((89781010679/10141204801825835211973625643008), (-303009583199/20282409603651670423947251286016)), (5/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((-27257404341/81129638414606681695789005144064), (109763816347/162259276829213363391578010288128)), (15/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179546088029/8589934592), (43543296143/17179869184)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((175818098267/137438953472), (10557043013/274877906944)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((84854239257/8796093022208), (-6527475199/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-34702433313/281474976710656), (2684054023/140737488355328)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((84600635439/36028797018963968), (-4954323827/9007199254740992)), (9/72057594037927936), by norm_num⟩
  | 5 => ⟨((-245852109591/4611686018427387904), (38922358271/2305843009213693952)), (25/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49273107547/36893488147419103232), (-79434996699/147573952589676412928)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-84032620087/2361183241434822606848), (83167281571/4722366482869645213696)), (69/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((298643816459/302231454903657293676544), (-44333646547/75557863725914323419136)), (85/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-2131906129/75557863725914323419136), (23947437729/1208925819614629174706176)), (57/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((127070950423/154742504910672534362390528), (-209022087709/309485009821345068724781056)), (159/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-119809073169/4951760157141521099596496896), (229761513987/9903520314283042199192993792)), (51/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((227464928145/316912650057057350374175801344), (-126997575415/158456325028528675187087900672)), (1/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((251651324211/147573952589676412928), (-97589666067/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-363487145147/1180591620717411303424), (86435766311/590295810358705651712)), (5/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((312903525139/9444732965739290427392), (-178293301079/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-51996288353/18889465931478580854784), (139833165687/75557863725914323419136)), (3/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((235113658045/1208925819614629174706176), (-23088072907/151115727451828646838272)), (1/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-237088837661/19342813113834066795298816), (216433447053/19342813113834066795298816)), (9/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((13697077599/19342813113834066795298816), (-1812528731/2417851639229258349412352)), (11/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-188785435715/4951760157141521099596496896), (116029185859/2475880078570760549798248448)), (3/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((9568978773/4951760157141521099596496896), (-219550533563/79228162514264337593543950336)), (11/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((-58785185563/633825300114114700748351602688), (198399131857/1267650600228229401496703205376)), (3/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((10708265991/2535301200456458802993406410752), (-172485997117/20282409603651670423947251286016)), (11/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-59119166057/324518553658426726783156020576256), (290134808795/649037107316853453566312041152512)), (5/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((76723320783/10384593717069655257060992658440192), (-118535898077/5192296858534827628530496329220096)), (17/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359092176087/17179869184), (10885824033/4294967296)), (9/17179869184), by norm_num⟩
  | 1 => ⟨((351636196449/274877906944), (10557043053/274877906944)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((169708479097/17592186044416), (-6527475365/8796093022208)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-138809736351/1125899906842624), (42944868535/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 4 => ⟨((42300321223/18014398509481984), (-79269203251/144115188075855872)), (19/144115188075855872), by norm_num⟩
  | 5 => ⟨((-245852166117/4611686018427387904), (4865298009/288230376151711744)), (13/2305843009213693952), by norm_num⟩
  | 6 => ⟨((6159141709/4611686018427387904), (-79435107327/147573952589676412928)), (33/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-84032710107/2361183241434822606848), (83167502879/4722366482869645213696)), (35/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((298644400503/302231454903657293676544), (-177335423707/302231454903657293676544)), (43/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-272884881503/9671406556917033397649408), (191581015497/9671406556917033397649408)), (115/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((254143208007/309485009821345068724781056), (-52256179909/77371252455336267181195264)), (5/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-14976246907/618970019642690137449562112), (229765941093/9903520314283042199192993792)), (205/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((227467269555/316912650057057350374175801344), (-254002385687/316912650057057350374175801344)), (257/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-15645176257/2361183241434822606848), (142634640863/37778931862957161709568)), (3/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((124791092047/75557863725914323419136), (-167799798825/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((-282136389653/1208925819614629174706176), (110822749953/604462909807314587353088)), (5/604462909807314587353088), by norm_num⟩
  | 3 => ⟨((237088837661/9671406556917033397649408), (-216433447053/9671406556917033397649408)), (5/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((-41091232797/19342813113834066795298816), (5437586193/2417851639229258349412352)), (5/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((49556176875/309485009821345068724781056), (-243661290303/1237940039285380274899124224)), (3/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((-107172562257/9903520314283042199192993792), (307370746987/19807040628566084398385987584)), (1/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((52906667007/79228162514264337593543950336), (-178559218671/158456325028528675187087900672)), (5/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((-96374393919/2535301200456458802993406410752), (48511686689/633825300114114700748351602688)), (3/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((5080553333/2535301200456458802993406410752), (-199467681047/40564819207303340847894502572032)), (13/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-31648369823/324518553658426726783156020576256), (195584231827/649037107316853453566312041152512)), (7/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((89725579725/20769187434139310514121985316880384), (-368240683519/20769187434139310514121985316880384)), (7/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((-27853023185/166153499473114484112975882535043072), (334513310263/332306998946228968225951765070086144)), (7/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359092176087/17179869184), (10885824033/4294967296)), (5/8589934592), by norm_num⟩
  | 1 => ⟨((351636196449/274877906944), (10557043053/274877906944)), (3/137438953472), by norm_num⟩
  | 2 => ⟨((169708479093/17592186044416), (-13054950727/17592186044416)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-277619472647/2251799813685248), (42944868485/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((169201284739/72057594037927936), (-79269202927/144115188075855872)), (5/36028797018963968), by norm_num⟩
  | 5 => ⟨((-245852165379/4611686018427387904), (19461191809/1152921504606846976)), (27/4611686018427387904), by norm_num⟩
  | 6 => ⟨((197092533091/147573952589676412928), (-79435105037/147573952589676412928)), (17/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-336130834121/9444732965739290427392), (166334995115/9444732965739290427392)), (71/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((149322194507/151115727451828646838272), (-177335400575/302231454903657293676544)), (87/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-136442431061/4835703278458516698824704), (47895241985/2417851639229258349412352)), (29/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((254143177825/309485009821345068724781056), (-104512313187/154742504910672534362390528)), (161/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-14976244233/618970019642690137449562112), (114882882751/4951760157141521099596496896)), (103/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((113733608215/158456325028528675187087900672), (-127001033335/158456325028528675187087900672)), (129/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((56997250435/1208925819614629174706176), (-11194217167/302231454903657293676544)), (9/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((-287380409287/19342813113834066795298816), (262343572187/19342813113834066795298816)), (13/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((99615109811/38685626227668133590597632), (-210912434153/77371252455336267181195264)), (11/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((-200226977273/618970019642690137449562112), (123061257729/309485009821345068724781056)), (3/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((162382670087/4951760157141521099596496896), (-232856626505/4951760157141521099596496896)), (13/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((-28056565837/9903520314283042199192993792), (189380989499/39614081257132168796771975168)), (3/9903520314283042199192993792), by norm_num⟩
  | 6 => ⟨((136287021703/633825300114114700748351602688), (-274409540867/633825300114114700748351602688)), (17/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-147797915141/10141204801825835211973625643008), (22666781937/633825300114114700748351602688)), (23/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((35964056617/40564819207303340847894502572032), (-111127404447/40564819207303340847894502572032)), (15/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((-15577357591/324518553658426726783156020576256), (31965337111/162259276829213363391578010288128)), (19/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((11605426327/5192296858534827628530496329220096), (-278761091885/20769187434139310514121985316880384)), (11/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((-26466968729/332306998946228968225951765070086144), (289959698671/332306998946228968225951765070086144)), (25/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((2465727119/2658455991569831745807614120560689152), (-289421935713/5316911983139663491615228241121378304)), (27/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359092176087/17179869184), (10885824033/4294967296)), (11/17179869184), by norm_num⟩
  | 1 => ⟨((351636196449/274877906944), (10557043053/274877906944)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((169708479093/17592186044416), (-13054950727/17592186044416)), (5/35184372088832), by norm_num⟩
  | 3 => ⟨((-34702434081/281474976710656), (21472434243/1125899906842624)), (9/2251799813685248), by norm_num⟩
  | 4 => ⟨((338402569483/144115188075855872), (-39634601467/72057594037927936)), (21/144115188075855872), by norm_num⟩
  | 5 => ⟨((-15365760337/288230376151711744), (38922383629/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 6 => ⟨((197092533123/147573952589676412928), (-79435105101/147573952589676412928)), (35/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-336130834259/9444732965739290427392), (166334995453/9444732965739290427392)), (9/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((149322194641/151115727451828646838272), (-177335401403/302231454903657293676544)), (11/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-136442431293/4835703278458516698824704), (191580969845/9671406556917033397649408)), (117/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((254143178517/309485009821345068724781056), (-816502463/1208925819614629174706176)), (81/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-239619908517/9903520314283042199192993792), (229765774143/9903520314283042199192993792)), (207/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((56866804181/79228162514264337593543950336), (-254002083921/316912650057057350374175801344)), (259/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-161369180083/309485009821345068724781056), (170831345933/309485009821345068724781056)), (11/309485009821345068724781056), by norm_num⟩
  | 1 => ⟨((243264775905/1237940039285380274899124224), (-299025333067/1237940039285380274899124224)), (9/618970019642690137449562112), by norm_num⟩
  | 2 => ⟨((-98643011015/2475880078570760549798248448), (70727001721/1237940039285380274899124224)), (9/2475880078570760549798248448), by norm_num⟩
  | 3 => ⟨((113623953075/19807040628566084398385987584), (-95869790289/9903520314283042199192993792)), (11/19807040628566084398385987584), by norm_num⟩
  | 4 => ⟨((-12936034615/19807040628566084398385987584), (208370321691/158456325028528675187087900672)), (13/158456325028528675187087900672), by norm_num⟩
  | 5 => ⟨((157120552867/2535301200456458802993406410752), (-96386131191/633825300114114700748351602688)), (29/2535301200456458802993406410752), by norm_num⟩
  | 6 => ⟨((-25488372433/5070602400912917605986812821504), (39378993063/2535301200456458802993406410752)), (3/2535301200456458802993406410752), by norm_num⟩
  | 7 => ⟨((56776900723/162259276829213363391578010288128), (-58254192379/40564819207303340847894502572032)), (19/162259276829213363391578010288128), by norm_num⟩
  | 8 => ⟨((-52874832475/2596148429267413814265248164610048), (158755973483/1298074214633706907132624082305024)), (13/1298074214633706907132624082305024), by norm_num⟩
  | 9 => ⟨((36845316723/41538374868278621028243970633760768), (-201830006373/20769187434139310514121985316880384)), (35/41538374868278621028243970633760768), by norm_num⟩
  | 10 => ⟨((-1029779771/83076749736557242056487941267521536), (241746827841/332306998946228968225951765070086144)), (11/166153499473114484112975882535043072), by norm_num⟩
  | 11 => ⟨((-7836007617/2658455991569831745807614120560689152), (-68721421249/1329227995784915872903807060280344576)), (29/5316911983139663491615228241121378304), by norm_num⟩
  | 12 => ⟨((39312829325/85070591730234615865843651857942052864), (298518260079/85070591730234615865843651857942052864)), (17/42535295865117307932921825928971026432), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359092176087/17179869184), (10885824033/4294967296)), (3/4294967296), by norm_num⟩
  | 1 => ⟨((351636196449/274877906944), (10557043053/274877906944)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((169708479093/17592186044416), (-13054950727/17592186044416)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-34702434081/281474976710656), (21472434243/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 4 => ⟨((338402569483/144115188075855872), (-39634601467/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 5 => ⟨((-15365760337/288230376151711744), (77844767257/4611686018427387904)), (29/4611686018427387904), by norm_num⟩
  | 6 => ⟨((98546266561/73786976294838206464), (-79435105099/147573952589676412928)), (9/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-21008177141/590295810358705651712), (166334995439/9444732965739290427392)), (73/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((74661097319/75557863725914323419136), (-88667700683/151115727451828646838272)), (89/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-272884862577/9671406556917033397649408), (191580969751/9671406556917033397649408)), (59/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((254143178513/309485009821345068724781056), (-209024630303/309485009821345068724781056)), (163/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-119809954273/4951760157141521099596496896), (229765773631/9903520314283042199192993792)), (13/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((113733608435/158456325028528675187087900672), (-254002082809/316912650057057350374175801344)), (65/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1029697818388627/1048576), (357573323541721/524288)), (322135/131072), by norm_num⟩
  | 1 => ⟨((-164148187617/128), (13356031985/16)), (421/128), by norm_num⟩
  | 2 => ⟨((-216384955381/256), (16531453517/32)), (285/128), by norm_num⟩
  | 3 => ⟨((-95940848591/256), (110268641247/512)), (65/64), by norm_num⟩
  | 4 => ⟨((-257441404267/2048), (69622710145/1024)), (45/128), by norm_num⟩
  | 5 => ⟨((-278618428313/8192), (35484328341/2048)), (403/4096), by norm_num⟩
  | 6 => ⟨((-126644248699/16384), (121580393153/32768)), (95/4096), by norm_num⟩
  | 7 => ⟨((-198882961247/131072), (11245596881/16384)), (621/131072), by norm_num⟩
  | 8 => ⟨((-275307073247/1048576), (58674680089/524288)), (449/524288), by norm_num⟩
  | 9 => ⟨((-341168237517/8388608), (136988055459/8388608)), (583/4194304), by norm_num⟩
  | 10 => ⟨((-95780693161/16777216), (144833135025/67108864)), (689/33554432), by norm_num⟩
  | 11 => ⟨((-393721188675/536870912), (140023918811/536870912)), (187/67108864), by norm_num⟩
  | 12 => ⟨((-23329742081/268435456), (62382745027/2147483648)), (1505/4294967296), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((805601422957249/5070602400912917605986812821504), (1650769404549/5070602400912917605986812821504)), (911/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((907426241071645/316912650057057350374175801344), (506919941783/79228162514264337593543950336)), (1123/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((482595203579199/9903520314283042199192993792), (1143702475955/9903520314283042199192993792)), (1267/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((483184424008001/618970019642690137449562112), (2435681434715/1237940039285380274899124224)), (675/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1814450943619747/154742504910672534362390528), (2441624875959/77371252455336267181195264)), (677/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1590159953443693/9671406556917033397649408), (2295357476635/4835703278458516698824704)), (1273/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1294369552779583/604462909807314587353088), (2014794960485/302231454903657293676544)), (559/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1945705256210289/75557863725914323419136), (821502666133/9444732965739290427392)), (57/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((83816070503035/295147905179352825856), (4950060292521/4722366482869645213696)), (1375/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((840709946263649/295147905179352825856), (6840716148275/590295810358705651712)), (1901/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1898642647106865/73786976294838206464), (1075349756977/9223372036854775808)), (2391/73786976294838206464), by norm_num⟩
  | 7 => ⟨((953750918862767/4611686018427387904), (4875025553367/4611686018427387904)), (339/1152921504606846976), by norm_num⟩
  | 6 => ⟨((209887944970983/144115188075855872), (1230092784415/144115188075855872)), (2741/1152921504606846976), by norm_num⟩
  | 5 => ⟨((634729500160309/72057594037927936), (4356902371525/72057594037927936)), (2431/144115188075855872), by norm_num⟩
  | 4 => ⟨((1604762529333741/36028797018963968), (13279870537547/36028797018963968)), (3711/36028797018963968), by norm_num⟩
  | 3 => ⟨((1632094221262063/9007199254740992), (16972387048963/9007199254740992)), (4755/9007199254740992), by norm_num⟩
  | 2 => ⟨((629494637559923/1125899906842624), (8772237082501/1125899906842624)), (617/281474976710656), by norm_num⟩
  | 1 => ⟨((665570344792671/562949953421312), (1737152679191/70368744177664)), (7871/1125899906842624), by norm_num⟩
  | 0 => ⟨((1559539654890565/1125899906842624), (61793816905471/1125899906842624)), (17715/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1559539654890565/1125899906842624), (61793816905471/1125899906842624)), (67577366355514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((269600504073479/140737488355328), (42796836248695/281474976710656)), (25511/562949953421312), by norm_num⟩
  | 2 => ⟨((513200429697133/140737488355328), (20495691589059/35184372088832)), (26375/140737488355328), by norm_num⟩
  | 3 => ⟨((113977053156367/8796093022208), (298950843968129/70368744177664)), (55771/35184372088832), by norm_num⟩
  | 4 => ⟨((20595680334749/137438953472), (484214073055913/4398046511104)), (239901/4398046511104), by norm_num⟩
  | 5 => ⟨((177546110319147/17179869184), (1133766802723401/34359738368)), (974415/34359738368), by norm_num⟩
  | 6 => ⟨((-1029697818388627/1048576), (357573323541721/524288)), (322135/131072), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((359092176087/17179869184), (10885824033/4294967296)), (3/4294967296), by norm_num⟩, 0, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/4707961), (-1624320/4707961)), 0, by norm_num⟩
  | 1 => ⟨((-1218346188800/22164896777521), (3659268096000/22164896777521)), 0, by norm_num⟩
  | 2 => ⟨((-16854017063/1099511627776), (-107711460035/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((106583439431/8796093022208), (1247220819/137438953472)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((-314163909579/70368744177664), (-1422630215/17592186044416)), (3/35184372088832), by norm_num⟩
  | 5 => ⟨((38073365643/35184372088832), (-1651070111/2199023255552)), (11/281474976710656), by norm_num⟩
  | 6 => ⟨((-4552057555/35184372088832), (103106904427/281474976710656)), (5/281474976710656), by norm_num⟩
  | 7 => ⟨((-72591599565/2251799813685248), (-123803582619/1125899906842624)), (17/2251799813685248), by norm_num⟩
  | 8 => ⟨((120164042595/4503599627370496), (93436932643/4503599627370496)), (29/9007199254740992), by norm_num⟩
  | 9 => ⟨((-179473463603/18014398509481984), (-13007638925/36028797018963968)), (3/2251799813685248), by norm_num⟩
  | 10 => ⟨((88123521591/36028797018963968), (-117618022713/72057594037927936)), (41/72057594037927936), by norm_num⟩
  | 11 => ⟨((-87511358835/288230376151711744), (234178438925/288230376151711744)), (69/288230376151711744), by norm_num⟩
  | 12 => ⟨((-19460137067/288230376151711744), (-284498379487/1152921504606846976)), (115/1152921504606846976), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (1269/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (1269/1280)))⁻¹=value ((2252800/4707961), (-1624320/4707961)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/4707961), (-1624320/4707961))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/10851961), (-1624320/10851961)), 0, by norm_num⟩
  | 1 => ⟨((-6251510988800/117765057545521), (6320553984000/117765057545521)), 0, by norm_num⟩
  | 2 => ⟨((12095898973/2199023255552), (-119585185327/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((4404261973/140737488355328), (400974766219/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-123194175957/562949953421312), (-286237497445/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((174035728535/2251799813685248), (168393636167/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 6 => ⟨((-87609324985/4503599627370496), (-68662908479/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 7 => ⟨((73105805141/18014398509481984), (-1606165747/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 8 => ⟨((-207785768355/288230376151711744), (1439798917/4503599627370496)), (13/288230376151711744), by norm_num⟩
  | 9 => ⟨((242853638897/2305843009213693952), (-256570584501/2305843009213693952)), (27/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-97353712911/9223372036854775808), (256698209871/9223372036854775808)), (29/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-7028640921/36893488147419103232), (-426465836803/73786976294838206464)), (15/18446744073709551616), by norm_num⟩
  | 12 => ⟨((34436941081/73786976294838206464), (301628496477/295147905179352825856)), (31/147573952589676412928), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (1269/1280)))⁻¹=value ((3891200/10851961), (-1624320/10851961)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/10851961), (-1624320/10851961))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6127679897600/51090609161521), (-9979822080000/51090609161521)), 0, by norm_num⟩
  | 1 => ⟨((-129383291/68719476736), (122509859309/1099511627776)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-45803933099/2199023255552), (-311260654813/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((212616346115/17592186044416), (54761209527/8796093022208)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((-18672789849/4398046511104), (1880572895/4398046511104)), (7/70368744177664), by norm_num⟩
  | 5 => ⟨((282832459077/281474976710656), (-232386178729/281474976710656)), (3/70368744177664), by norm_num⟩
  | 6 => ⟨((-123763510513/1125899906842624), (105252620317/281474976710656)), (21/1125899906842624), by norm_num⟩
  | 7 => ⟨((-10216228151/281474976710656), (-247406394519/2251799813685248)), (9/1125899906842624), by norm_num⟩
  | 8 => ⟨((246821390451/9007199254740992), (45998566863/2251799813685248)), (15/4503599627370496), by norm_num⟩
  | 9 => ⟨((-181370757657/18014398509481984), (-4499361771/18014398509481984)), (25/18014398509481984), by norm_num⟩
  | 10 => ⟨((22125952383/9007199254740992), (-59811738739/36028797018963968)), (21/36028797018963968), by norm_num⟩
  | 11 => ⟨((-43728223789/144115188075855872), (58961080275/72057594037927936)), (69/288230376151711744), by norm_num⟩
  | 12 => ⟨((-1224666023/18014398509481984), (-285676615801/1152921504606846976)), (57/576460752303423488), by norm_num⟩
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
  | 0 => ⟨((27/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((204800/750843), (-60160/750843)), 0, by norm_num⟩
  | 1 => ⟨((-2129100800/62640578961), (12320768000/563765210649)), 0, by norm_num⟩
  | 2 => ⟨((1591570595840000/423299162059327107), (-1838036811776000/423299162059327107)), 0, by norm_num⟩
  | 3 => ⟨((-95370334829/281474976710656), (209083498965/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((37043063731/2251799813685248), (-258684065411/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((10622745265/4503599627370496), (147053398141/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((-140618572913/144115188075855872), (-307264312023/144115188075855872)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((125948313413/576460752303423488), (2266956847/9007199254740992)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-183913507977/4611686018427387904), (-117928281945/4611686018427387904)), (9/4611686018427387904), by norm_num⟩
  | 9 => ⟨((238452256333/36893488147419103232), (34860751189/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-70626572639/73786976294838206464), (44166393/36893488147419103232)), (21/295147905179352825856), by norm_num⟩
  | 11 => ⟨((19257032397/147573952589676412928), (-90926815103/2361183241434822606848)), (15/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-307021769195/18889465931478580854784), (197952758897/18889465931478580854784)), (43/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (1269/1280)))⁻¹=value ((204800/750843), (-60160/750843)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((204800/750843), (-60160/750843))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((75044848521/4398046511104), (-69147823189/1099511627776)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((75702093433/8796093022208), (175054613135/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-198526730307/17592186044416), (-229869598423/17592186044416)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((103052583721/17592186044416), (36234145981/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((-35275971231/17592186044416), (57784976457/140737488355328)), (1/17592186044416), by norm_num⟩
  | 5 => ⟨((261741914589/562949953421312), (-124419982279/281474976710656)), (7/281474976710656), by norm_num⟩
  | 6 => ⟨((-25739940467/562949953421312), (213596421195/1125899906842624)), (3/281474976710656), by norm_num⟩
  | 7 => ⟨((-90376065251/4503599627370496), (-246638884589/4503599627370496)), (21/4503599627370496), by norm_num⟩
  | 8 => ⟨((126477744821/9007199254740992), (90442170471/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 9 => ⟨((-183151619945/36028797018963968), (-2460860377/36028797018963968)), (57/72057594037927936), by norm_num⟩
  | 10 => ⟨((44424805921/36028797018963968), (-30407211495/36028797018963968)), (47/144115188075855872), by norm_num⟩
  | 11 => ⟨((-87363924929/576460752303423488), (118749551905/288230376151711744)), (39/288230376151711744), by norm_num⟩
  | 12 => ⟨((-39467720899/1152921504606846976), (-143421385019/1152921504606846976)), (1/18014398509481984), by norm_num⟩
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
  | 0 => ⟨((35/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/32970361), (-1624320/32970361)), 0, by norm_num⟩
  | 1 => ⟨((-24370904268800/1087044704470321), (11643125760000/1087044704470321)), 0, by norm_num⟩
  | 2 => ⟨((305855401539/140737488355328), (-30198085055/17592186044416)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-218373185553/1125899906842624), (270362345771/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((68312508229/4503599627370496), (-139074317521/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((-63999994067/72057594037927936), (268810179265/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((2683404903/576460752303423488), (-492754770949/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((92437221037/9223372036854775808), (107392928293/2305843009213693952)), (11/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-41259843213/18446744073709551616), (-177676089937/36893488147419103232)), (13/73786976294838206464), by norm_num⟩
  | 9 => ⟨((213550331149/590295810358705651712), (276501391201/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-240198220873/4722366482869645213696), (-49592659851/1180591620717411303424)), (17/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((123987616891/18889465931478580854784), (62587241257/18889465931478580854784)), (19/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-120157003509/151115727451828646838272), (-59988370637/302231454903657293676544)), (21/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (1269/1280)))⁻¹=value ((7168000/32970361), (-1624320/32970361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/32970361), (-1624320/32970361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21509914447/35184372088832), (-510641235581/35184372088832)), (3/35184372088832), by norm_num⟩
  | 1 => ⟨((36266807551/8796093022208), (86396397953/8796093022208)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((-133254061889/35184372088832), (-228764837923/70368744177664)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((262727231821/140737488355328), (59009962537/140737488355328)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-177040459541/281474976710656), (53046630507/281474976710656)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((161043527771/1125899906842624), (-174498914305/1125899906842624)), (11/1125899906842624), by norm_num⟩
  | 6 => ⟨((-55506557899/4503599627370496), (143818635635/2251799813685248)), (19/4503599627370496), by norm_num⟩
  | 7 => ⟨((-131403849835/18014398509481984), (-327212681805/18014398509481984)), (1/562949953421312), by norm_num⟩
  | 8 => ⟨((43125088195/9007199254740992), (14798955309/4503599627370496)), (27/36028797018963968), by norm_num⟩
  | 9 => ⟨((-30803761251/18014398509481984), (-1058009157/288230376151711744)), (87/288230376151711744), by norm_num⟩
  | 10 => ⟨((237767362901/576460752303423488), (-10302591777/36028797018963968)), (73/576460752303423488), by norm_num⟩
  | 11 => ⟨((-14539280465/288230376151711744), (318855776067/2305843009213693952)), (119/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-53006720347/4611686018427387904), (-383995484479/9223372036854775808)), (195/9223372036854775808), by norm_num⟩
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
  | 0 => ⟨((43/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/48944761), (-1624320/48944761)), 0, by norm_num⟩
  | 1 => ⟨((-37457132748800/2395589629347121), (14304411648000/2395589629347121)), 0, by norm_num⟩
  | 2 => ⟨((46005774711/35184372088832), (-112116015717/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-235117091451/2251799813685248), (52559287427/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((141305644307/18014398509481984), (-91259525373/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-77468939445/144115188075855872), (37529274127/36028797018963968)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((71653718547/2305843009213693952), (-118323229439/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-40310215171/36893488147419103232), (179826555375/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-18731636015/295147905179352825856), (-1032007109/1152921504606846976)), (11/295147905179352825856), by norm_num⟩
  | 9 => ⟨((48552169655/2361183241434822606848), (375308039133/4722366482869645213696)), (5/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-119707194633/37778931862957161709568), (-257219292205/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((60149272341/151115727451828646838272), (84615110675/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-27260959289/604462909807314587353088), (-211651774407/4835703278458516698824704)), (7/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (1269/1280)))⁻¹=value ((8806400/48944761), (-1624320/48944761)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/48944761), (-1624320/48944761))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-26152742321/70368744177664), (-370364457291/140737488355328)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((40282928779/35184372088832), (261912112829/140737488355328)), (5/140737488355328), by norm_num⟩
  | 2 => ⟨((-32482223149/35184372088832), (-85520635551/140737488355328)), (5/281474976710656), by norm_num⟩
  | 3 => ⟨((249349792179/562949953421312), (14872016637/281474976710656)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((-332451738323/2251799813685248), (129205527201/2251799813685248)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((74133761245/2251799813685248), (-181245494491/4503599627370496)), (13/4503599627370496), by norm_num⟩
  | 6 => ⟨((-43089326209/18014398509481984), (18090222109/1125899906842624)), (11/9007199254740992), by norm_num⟩
  | 7 => ⟨((-8857109967/4503599627370496), (-20316766603/4503599627370496)), (37/72057594037927936), by norm_num⟩
  | 8 => ⟨((176150722533/144115188075855872), (58046317049/72057594037927936)), (31/144115188075855872), by norm_num⟩
  | 9 => ⟨((-497039325215/1152921504606846976), (4495873581/1152921504606846976)), (25/288230376151711744), by norm_num⟩
  | 10 => ⟨((59629983783/576460752303423488), (-41875902407/576460752303423488)), (83/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-116097997781/9223372036854775808), (321028949607/9223372036854775808)), (17/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-13350279485/4611686018427387904), (-192758644927/18446744073709551616)), (111/18446744073709551616), by norm_num⟩
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
  | 0 => ⟨((51/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/22731987), (-180480/7577329)), 0, by norm_num⟩
  | 1 => ⟨((-5914190643200/516743232968169), (209453056000/57415914774241)), 0, by norm_num⟩
  | 2 => ⟨((234472890005/281474976710656), (-116998863247/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-264998550043/4503599627370496), (188033274467/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((72216319295/18014398509481984), (-140443061721/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((-150207787177/576460752303423488), (6237556043/18014398509481984)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((18251419765/1152921504606846976), (-273187595297/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-126848023565/147573952589676412928), (362550382077/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((43169970135/1180591620717411303424), (-58549039471/295147905179352825856)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-4134684803/9444732965739290427392), (295179226319/18889465931478580854784)), (3/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-46113418269/302231454903657293676544), (-363249675211/302231454903657293676544)), (9/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((31429402207/1208925819614629174706176), (109072948179/1208925819614629174706176)), (7/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-59293035417/19342813113834066795298816), (-255309835149/38685626227668133590597632)), (21/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (1269/1280)))⁻¹=value ((3481600/22731987), (-180480/7577329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/22731987), (-180480/7577329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-67330129493/562949953421312), (-221914716545/562949953421312)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((131467105641/562949953421312), (20162127439/70368744177664)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((-199470742977/1125899906842624), (-101600872571/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 3 => ⟨((377129504649/4503599627370496), (5275722617/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-31171685431/1125899906842624), (118196249983/9007199254740992)), (13/9007199254740992), by norm_num⟩
  | 5 => ⟨((217888662829/36028797018963968), (-37301424275/4503599627370496)), (23/36028797018963968), by norm_num⟩
  | 6 => ⟨((-3135687307/9007199254740992), (116161217971/36028797018963968)), (39/144115188075855872), by norm_num⟩
  | 7 => ⟨((-30293043933/72057594037927936), (-258005816805/288230376151711744)), (17/144115188075855872), by norm_num⟩
  | 8 => ⟨((143680441221/576460752303423488), (90969516199/576460752303423488)), (7/144115188075855872), by norm_num⟩
  | 9 => ⟨((-200382855039/2305843009213693952), (2016747423/1152921504606846976)), (91/4611686018427387904), by norm_num⟩
  | 10 => ⟨((95677723033/4611686018427387904), (-68062150071/4611686018427387904)), (75/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-46335488805/18446744073709551616), (129273645891/18446744073709551616)), (123/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-86090042347/147573952589676412928), (-309617809715/147573952589676412928)), (199/147573952589676412928), by norm_num⟩
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
  | 0 => ⟨((59/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/90723961), (-1624320/90723961)), 0, by norm_num⟩
  | 1 => ⟨((-71682653388800/8230837099529521), (19626983424000/8230837099529521)), 0, by norm_num⟩
  | 2 => ⟨((157236435867/281474976710656), (-133283571777/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-315977688181/9007199254740992), (5845469615/281474976710656)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((4841863633/2251799813685248), (-122281794505/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-147572202969/1152921504606846976), (19060311193/144115188075855872)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((135396565015/18446744073709551616), (-183605819273/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-117965675685/295147905179352825856), (107511760159/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 8 => ⟨((23723299469/1180591620717411303424), (-30750269017/590295810358705651712)), (11/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-64328657/73786976294838206464), (275704904363/75557863725914323419136)), (15/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((30696908631/1208925819614629174706176), (-9474882805/37778931862957161709568)), (19/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((10720065103/19342813113834066795298816), (327449770649/19342813113834066795298816)), (23/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-29161685395/154742504910672534362390528), (-347359459101/309485009821345068724781056)), (29/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (1269/1280)))⁻¹=value ((12083200/90723961), (-1624320/90723961)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/90723961), (-1624320/90723961))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-51762463637/2251799813685248), (-226804403041/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((172104347489/4503599627370496), (167207190761/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 2 => ⟨((-63250619433/2251799813685248), (-12359083621/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((237136482709/18014398509481984), (-3187123429/4503599627370496)), (9/18014398509481984), by norm_num⟩
  | 4 => ⟨((-311486057895/72057594037927936), (43385634301/18014398509481984)), (19/72057594037927936), by norm_num⟩
  | 5 => ⟨((66543426715/72057594037927936), (-6352251069/4503599627370496)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((-21624379913/576460752303423488), (310042318827/576460752303423488)), (29/576460752303423488), by norm_num⟩
  | 7 => ⟨((-42851098623/576460752303423488), (-42613555663/288230376151711744)), (51/2305843009213693952), by norm_num⟩
  | 8 => ⟨((97526180987/2305843009213693952), (118683178869/4611686018427387904)), (21/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-134567469689/9223372036854775808), (8369310105/18446744073709551616)), (17/4611686018427387904), by norm_num⟩
  | 10 => ⟨((127890400117/36893488147419103232), (-184313993943/73786976294838206464)), (111/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-123241077127/295147905179352825856), (21688036409/18446744073709551616)), (91/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-14459115159/147573952589676412928), (-207205476997/590295810358705651712)), (295/1180591620717411303424), by norm_num⟩
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
  | 0 => ⟨((67/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/116528761), (-1624320/116528761)), 0, by norm_num⟩
  | 1 => ⟨((-92821945548800/13578952140195121), (22288269312000/13578952140195121)), 0, by norm_num⟩
  | 2 => ⟨((220126531985/562949953421312), (-81223072171/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-198306817023/9007199254740992), (50530578817/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((43884979793/36028797018963968), (-117315896605/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((-152280345467/2305843009213693952), (65044708005/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((8059053971/2305843009213693952), (-279057211151/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-211819395885/1180591620717411303424), (145818314159/590295810358705651712)), (11/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((41754323887/4722366482869645213696), (-149174627893/9444732965739290427392)), (13/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-62032062949/151115727451828646838272), (299676656251/302231454903657293676544)), (15/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((10431652351/604462909807314587353088), (-296137228981/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-45591495711/77371252455336267181195264), (72068582855/19342813113834066795298816)), (9/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((10801694221/1237940039285380274899124224), (-276645196241/1237940039285380274899124224)), (5/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (1269/1280)))⁻¹=value ((13721600/116528761), (-1624320/116528761)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/116528761), (-1624320/116528761))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-30703674435/9007199254740992), (-25263820379/4503599627370496)), (7/36028797018963968), by norm_num⟩
  | 1 => ⟨((23676465141/4503599627370496), (18670579753/4503599627370496)), (9/36028797018963968), by norm_num⟩
  | 2 => ⟨((-273745681191/72057594037927936), (-79874962451/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 3 => ⟨((255314186861/144115188075855872), (-8215912473/36028797018963968)), (11/144115188075855872), by norm_num⟩
  | 4 => ⟨((-333286508977/576460752303423488), (213073423935/576460752303423488)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((138978656411/1152921504606846976), (-59015940483/288230376151711744)), (23/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-11945875755/4611686018427387904), (176973688977/2305843009213693952)), (37/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-1613570943/144115188075855872), (-192859711383/9223372036854775808)), (33/9223372036854775808), by norm_num⟩
  | 8 => ⟨((14167227023/2305843009213693952), (132591906277/36893488147419103232)), (27/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-309677955433/147573952589676412928), (3247382949/36893488147419103232)), (43/73786976294838206464), by norm_num⟩
  | 10 => ⟨((146483369581/295147905179352825856), (-213843590613/590295810358705651712)), (35/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-140433469801/2361183241434822606848), (399162084925/2361183241434822606848)), (57/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-2081784687/147573952589676412928), (-237702839607/4722366482869645213696)), (185/4722366482869645213696), by norm_num⟩
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
  | 0 => ⟨((75/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/48536787), (-180480/16178929)), 0, by norm_num⟩
  | 1 => ⟨((-12960621363200/2355819692283369), (308019200000/261757743587041)), 0, by norm_num⟩
  | 2 => ⟨((159656411275/562949953421312), (-26106959991/281474976710656)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-130073730821/9007199254740992), (58311175419/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((104564894085/144115188075855872), (-121633214481/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-165628998521/4611686018427387904), (121308942951/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((257895590281/147573952589676412928), (-234306387975/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-49181770995/590295810358705651712), (220745340203/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((73158720867/18889465931478580854784), (-203842426437/37778931862957161709568)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-26321349137/151115727451828646838272), (185079467911/604462909807314587353088)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((144666124099/19342813113834066795298816), (-41395925149/2417851639229258349412352)), (1/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-92529120675/309485009821345068724781056), (146190568431/154742504910672534362390528)), (1/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((25996138155/2475880078570760549798248448), (-127498376671/2475880078570760549798248448)), (1/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (1269/1280)))⁻¹=value ((5120000/48536787), (-180480/16178929)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/48536787), (-180480/16178929))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3802486945/9007199254740992), (-19950008079/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 1 => ⟨((180481387743/288230376151711744), (29220980285/72057594037927936)), (5/144115188075855872), by norm_num⟩
  | 2 => ⟨((-258483393935/576460752303423488), (-53292967305/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((240386934929/1152921504606846976), (-47779983097/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 4 => ⟨((-311893447665/4611686018427387904), (224998450243/4611686018427387904)), (13/2305843009213693952), by norm_num⟩
  | 5 => ⟨((126607518369/9223372036854775808), (-238829656609/9223372036854775808)), (13/4611686018427387904), by norm_num⟩
  | 6 => ⟨((123410437/36893488147419103232), (44121546493/4611686018427387904)), (41/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-6769350447/4611686018427387904), (-190770265765/73786976294838206464)), (37/73786976294838206464), by norm_num⟩
  | 8 => ⟨((115115057763/147573952589676412928), (16186989417/36893488147419103232)), (15/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-311638460073/1180591620717411303424), (16414372347/1180591620717411303424)), (47/590295810358705651712), by norm_num⟩
  | 10 => ⟨((146765512951/2361183241434822606848), (-108511251373/2361183241434822606848)), (153/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-69987376239/9444732965739290427392), (401718776463/18889465931478580854784)), (31/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-33573373021/18889465931478580854784), (-238588990893/37778931862957161709568)), (101/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((83/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/177968761), (-1624320/177968761)), 0, by norm_num⟩
  | 1 => ⟨((-143153593548800/31672879891875121), (27610841088000/31672879891875121)), 0, by norm_num⟩
  | 2 => ⟨((119272341135/562949953421312), (-35048021867/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-354311127341/36028797018963968), (70978456185/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((130183269975/288230376151711744), (-134340656767/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((-189138918693/9223372036854775808), (121661567253/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((67819580507/73786976294838206464), (-106772631325/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-191693488865/4722366482869645213696), (91489552971/2361183241434822606848)), (3/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((133113967333/75557863725914323419136), (-76906162251/37778931862957161709568)), (3/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-5655161097/75557863725914323419136), (127248538691/1208925819614629174706176)), (11/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((119694417597/38685626227668133590597632), (-207676377133/38685626227668133590597632)), (5/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-152591336649/1237940039285380274899124224), (654010173/2417851639229258349412352)), (9/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((92146500391/19807040628566084398385987584), (-66751332169/4951760157141521099596496896)), (1/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (1269/1280)))⁻¹=value ((16998400/177968761), (-1624320/177968761)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/177968761), (-1624320/177968761))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-26157397227/576460752303423488), (-113066996499/2305843009213693952)), (15/4611686018427387904), by norm_num⟩
  | 1 => ⟨((151954252193/2305843009213693952), (81056045497/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-13540856675/288230376151711744), (-28203175415/4611686018427387904)), (23/9223372036854775808), by norm_num⟩
  | 3 => ⟨((100571705649/4611686018427387904), (-26672362625/4611686018427387904)), (25/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-32417694433/4611686018427387904), (208558061823/36893488147419103232)), (25/36893488147419103232), by norm_num⟩
  | 5 => ⟨((51085207265/36893488147419103232), (-107011455529/36893488147419103232)), (25/73786976294838206464), by norm_num⟩
  | 6 => ⟨((10256401945/295147905179352825856), (78112205703/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-100520760321/590295810358705651712), (-335220055691/1180591620717411303424)), (71/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((103818725897/1180591620717411303424), (112321379367/2361183241434822606848)), (29/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-69660321873/2361183241434822606848), (17630740623/9444732965739290427392)), (23/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((261349162203/37778931862957161709568), (-195715151427/37778931862957161709568)), (147/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-123975932183/151115727451828646838272), (359334075043/151115727451828646838272)), (239/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-30083195275/151115727451828646838272), (-425715020059/604462909807314587353088)), (97/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((91/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/213603961), (-1624320/213603961)), 0, by norm_num⟩
  | 1 => ⟨((-172345949388800/45626652154889521), (30272126976000/45626652154889521)), 0, by norm_num⟩
  | 2 => ⟨((365379641157/2251799813685248), (-97516105863/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-1946098607/281474976710656), (45146758687/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((336755770201/1152921504606846976), (-156356751937/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((-112770877667/9223372036854775808), (129622639241/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((299082689047/590295810358705651712), (-104196689013/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-196080510977/9444732965739290427392), (163652085125/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((126907381163/151115727451828646838272), (-252313573953/302231454903657293676544)), (3/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-40452966863/1208925819614629174706176), (95777137949/2417851639229258349412352)), (5/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((50645314951/38685626227668133590597632), (-287095273975/154742504910672534362390528)), (1/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-61967611683/1237940039285380274899124224), (106357465795/1237940039285380274899124224)), (13/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((147131268087/79228162514264337593543950336), (-312026880369/79228162514264337593543950336)), (21/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (1269/1280)))⁻¹=value ((18636800/213603961), (-1624320/213603961)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/213603961), (-1624320/213603961))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-79909293679/18446744073709551616), (-72555024071/18446744073709551616)), (13/36893488147419103232), by norm_num⟩
  | 1 => ⟨((229512305301/36893488147419103232), (25096963035/9223372036854775808)), (15/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-326665859365/73786976294838206464), (-10012311391/36893488147419103232)), (5/18446744073709551616), by norm_num⟩
  | 3 => ⟨((18934826383/9223372036854775808), (-99678651843/147573952589676412928)), (11/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-194006217369/295147905179352825856), (172350076735/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
  | 5 => ⟨((147821289589/1180591620717411303424), (-344230125783/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((15887023449/2361183241434822606848), (248621557269/2361183241434822606848)), (35/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-41818103873/2361183241434822606848), (-66223486635/2361183241434822606848)), (61/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((336743224387/37778931862957161709568), (87607939589/18889465931478580854784)), (25/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-448261112893/151115727451828646838272), (16530503761/75557863725914323419136)), (159/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((52343265423/75557863725914323419136), (-4962516431/9444732965739290427392)), (127/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-98794661571/1208925819614629174706176), (289250048077/1208925819614629174706176)), (103/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-97049509995/4835703278458516698824704), (-341802616779/4835703278458516698824704)), (167/2417851639229258349412352), by norm_num⟩
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
  | 0 => ⟨((99/8), (1269/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/28057329), (-60160/9352443)), 0, by norm_num⟩
  | 1 => ⟨((-2521267404800/787213710614241), (135528448000/262404570204747)), 0, by norm_num⟩
  | 2 => ⟨((285795254067/2251799813685248), (-8735873049/281474976710656)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-359963755877/72057594037927936), (119196934757/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((1758483689/9007199254740992), (-95089055207/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-17461101529/2305843009213693952), (145325382329/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 6 => ⟨((42994369663/147573952589676412928), (-107725463097/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-52462381195/4722366482869645213696), (19511651919/2361183241434822606848)), (1/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((31690636405/75557863725914323419136), (-222128307525/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-151419006023/9671406556917033397649408), (155728824981/9671406556917033397649408)), (9/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((44624461357/77371252455336267181195264), (-53911617763/77371252455336267181195264)), (7/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-207118829357/9903520314283042199192993792), (295408681919/9903520314283042199192993792)), (5/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((29459820631/39614081257132168796771975168), (-200411802549/158456325028528675187087900672)), (15/158456325028528675187087900672), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (1269/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (1269/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (1269/1280)))⁻¹=value ((2252800/28057329), (-60160/9352443)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/28057329), (-60160/9352443))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-110125600363/295147905179352825856), (-84985953669/295147905179352825856)), (19/590295810358705651712), by norm_num⟩
  | 1 => ⟨((157285861965/295147905179352825856), (27865115449/147573952589676412928)), (23/590295810358705651712), by norm_num⟩
  | 2 => ⟨((-111924533463/295147905179352825856), (484699059/590295810358705651712)), (31/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((207442979155/1180591620717411303424), (-81096903423/1180591620717411303424)), (9/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-263767295271/4722366482869645213696), (257074390277/4722366482869645213696)), (17/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((96762573569/9444732965739290427392), (-251058296303/9444732965739290427392)), (17/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((33689330601/37778931862957161709568), (44915774707/4722366482869645213696)), (55/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-15761752361/9444732965739290427392), (-47544795385/18889465931478580854784)), (3/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((248016519001/302231454903657293676544), (15517174439/37778931862957161709568)), (39/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-163830244465/604462909807314587353088), (27560236425/1208925819614629174706176)), (125/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((304897304649/4835703278458516698824704), (-117099231473/2417851639229258349412352)), (99/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-71549598631/9671406556917033397649408), (52911789229/2417851639229258349412352)), (161/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-17790321963/9671406556917033397649408), (-62366979849/9671406556917033397649408)), (65/9671406556917033397649408), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((309394306189/549755813888), (7775022607/274877906944)), (231/137438953472), by norm_num⟩
  | 1 => ⟨((73406866187/1099511627776), (259294449257/1099511627776)), (561/137438953472), by norm_num⟩
  | 2 => ⟨((-5561242489/1099511627776), (-13438413009/2199023255552)), (87077/17592186044416), by norm_num⟩
  | 3 => ⟨((242513025063/17592186044416), (227723114279/17592186044416)), (75331/17592186044416), by norm_num⟩
  | 4 => ⟨((-285996677359/70368744177664), (50957303361/35184372088832)), (26351/8796093022208), by norm_num⟩
  | 5 => ⟨((142952971339/140737488355328), (-93307704679/140737488355328)), (248949/140737488355328), by norm_num⟩
  | 6 => ⟨((-62433544039/562949953421312), (221074697473/562949953421312)), (126205/140737488355328), by norm_num⟩
  | 7 => ⟨((-82009598559/2251799813685248), (-242028132341/2251799813685248)), (112537/281474976710656), by norm_num⟩
  | 8 => ⟨((246275781427/9007199254740992), (186027670745/9007199254740992)), (1454099/9007199254740992), by norm_num⟩
  | 9 => ⟨((-362824005841/36028797018963968), (-8139973741/36028797018963968)), (2175913/36028797018963968), by norm_num⟩
  | 10 => ⟨((44232307229/18014398509481984), (-29868588839/18014398509481984)), (95827/4503599627370496), by norm_num⟩
  | 11 => ⟨((-87455857159/288230376151711744), (117944285755/144115188075855872)), (2064873/288230376151711744), by norm_num⟩
  | 12 => ⟨((-19598601651/288230376151711744), (-35706841947/144115188075855872)), (2693813/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((309394306189/549755813888), (7775022607/274877906944)), (925/549755813888), by norm_num⟩
  | 1 => ⟨((73406866187/1099511627776), (259294449257/1099511627776)), (4489/1099511627776), by norm_num⟩
  | 2 => ⟨((-5561242489/1099511627776), (-13438413009/2199023255552)), (43539/8796093022208), by norm_num⟩
  | 3 => ⟨((242513025063/17592186044416), (227723114279/17592186044416)), (18833/4398046511104), by norm_num⟩
  | 4 => ⟨((-285996677359/70368744177664), (50957303361/35184372088832)), (210811/70368744177664), by norm_num⟩
  | 5 => ⟨((142952971339/140737488355328), (-93307704679/140737488355328)), (248955/140737488355328), by norm_num⟩
  | 6 => ⟨((-62433544039/562949953421312), (221074697473/562949953421312)), (504843/562949953421312), by norm_num⟩
  | 7 => ⟨((-82009598559/2251799813685248), (-242028132341/2251799813685248)), (900387/2251799813685248), by norm_num⟩
  | 8 => ⟨((246275781427/9007199254740992), (186027670745/9007199254740992)), (363615/2251799813685248), by norm_num⟩
  | 9 => ⟨((-362824005841/36028797018963968), (-8139973741/36028797018963968)), (2177355/36028797018963968), by norm_num⟩
  | 10 => ⟨((44232307229/18014398509481984), (-29868588839/18014398509481984)), (1536115/72057594037927936), by norm_num⟩
  | 11 => ⟨((-87455857159/288230376151711744), (117944285755/144115188075855872)), (2076403/288230376151711744), by norm_num⟩
  | 12 => ⟨((-19598601651/288230376151711744), (-35706841947/144115188075855872)), (1369965/576460752303423488), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile004Gamma
