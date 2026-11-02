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
namespace Reinmann.XiRectangle.Tile008Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2397/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2397/640))
  have he : value ((3/4), (2397/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/298840009), (-3068160/298840009)), 0, by norm_num⟩
  | 1 => ⟨((-235396129587200/89305350979120081), (67234430976000/89305350979120081)), 0, by norm_num⟩
  | 2 => ⟨((26114526655/281474976710656), (-11578255255/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-28737215125/9007199254740992), (35748337883/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((7695020879/72057594037927936), (-51383509359/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-63785410913/18446744073709551616), (35199413015/9223372036854775808)), (7/18446744073709551616), by norm_num⟩
  | 6 => ⟨((31636275811/295147905179352825856), (-46537157223/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-29472961195/9444732965739290427392), (1868661777/295147905179352825856)), (9/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((6189149543/75557863725914323419136), (-74999284345/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-1045363325/604462909807314587353088), (92060579301/9671406556917033397649408)), (19/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((4500933777/309485009821345068724781056), (-110758726773/309485009821345068724781056)), (13/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((6456801645/4951760157141521099596496896), (32672091373/2475880078570760549798248448)), (9/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-18309632765/158456325028528675187087900672), (-18901294873/39614081257132168796771975168)), (25/158456325028528675187087900672), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (2397/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (2397/1280)))⁻¹=value ((21913600/298840009), (-3068160/298840009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/298840009), (-3068160/298840009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44720816003/17179869184), (4779693839/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((10956800/298840009), (-1534080/298840009)), 0, by norm_num⟩
  | 2 => ⟨((-58849032396800/89305350979120081), (16808607744000/89305350979120081)), 0, by norm_num⟩
  | 3 => ⟨((69638737747/4503599627370496), (-30875347347/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-28737215125/72057594037927936), (35748337883/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((24624066813/2305843009213693952), (-41106807487/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-42523607275/147573952589676412928), (46932550687/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 7 => ⟨((4519467973/590295810358705651712), (-53185322541/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-29472961195/151115727451828646838272), (1868661777/4722366482869645213696)), (9/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((11002932521/2417851639229258349412352), (-66666030529/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-209072665/2417851639229258349412352), (73648463441/154742504910672534362390528)), (1/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((3273406383/4951760157141521099596496896), (-80551801289/4951760157141521099596496896)), (5/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((2152267215/39614081257132168796771975168), (87125576995/158456325028528675187087900672)), (25/158456325028528675187087900672), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (51/20480)), 0, by norm_num⟩
  | 45 => ⟨((106382365817/4080638361600), (-101337/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-50964760702831/1915179604377600), (2135372846089/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((29906720481/1099511627776), (-63662589/17179869184)), (1/4398046511104), by norm_num⟩
  | 42 => ⟨((-61217094057/2199023255552), (8337540247/2199023255552)), (1/2199023255552), by norm_num⟩
  | 41 => ⟨((62702308865/2199023255552), (-8532788559/2199023255552)), (1/2199023255552), by norm_num⟩
  | 40 => ⟨((-32131996349/1099511627776), (8738652535/2199023255552)), (1/2199023255552), by norm_num⟩
  | 39 => ⟨((65905742215/2199023255552), (-8955208155/2199023255552)), (1/2199023255552), by norm_num⟩
  | 38 => ⟨((-67633567215/2199023255552), (4591444421/1099511627776)), (1/2199023255552), by norm_num⟩
  | 37 => ⟨((34727209223/1099511627776), (-4711234549/1099511627776)), (1/2199023255552), by norm_num⟩
  | 36 => ⟨((-35688014747/1099511627776), (9674889511/2199023255552)), (1/2199023255552), by norm_num⟩
  | 35 => ⟨((73407006817/2199023255552), (-1242651193/274877906944)), (1/2199023255552), by norm_num⟩
  | 34 => ⟨((-75556962369/2199023255552), (10222610323/2199023255552)), (1/1099511627776), by norm_num⟩
  | 33 => ⟨((38918333897/1099511627776), (-10520410619/2199023255552)), (1/1099511627776), by norm_num⟩
  | 32 => ⟨((-40129117751/1099511627776), (10836087519/2199023255552)), (1/1099511627776), by norm_num⟩
  | 31 => ⟨((82835334123/2199023255552), (-2792825251/549755813888)), (1/1099511627776), by norm_num⟩
  | 30 => ⟨((-42791723387/1099511627776), (5763961603/1099511627776)), (1/1099511627776), by norm_num⟩
  | 29 => ⟨((88520182519/2199023255552), (-1488509179/274877906944)), (1/2199023255552), by norm_num⟩
  | 28 => ⟨((-91665654277/2199023255552), (12314160363/2199023255552)), (1/2199023255552), by norm_num⟩
  | 27 => ⟨((95042940331/2199023255552), (-12748933209/2199023255552)), (1/2199023255552), by norm_num⟩
  | 26 => ⟨((-24669662957/549755813888), (13215544119/2199023255552)), (1/2199023255552), by norm_num⟩
  | 25 => ⟨((12825454479/274877906944), (-13717624837/2199023255552)), (1/2199023255552), by norm_num⟩
  | 24 => ⟨((-53426926621/1099511627776), (14259381569/2199023255552)), (1/2199023255552), by norm_num⟩
  | 23 => ⟨((6966967785/137438953472), (-927857081/137438953472)), (1/1099511627776), by norm_num⟩
  | 22 => ⟨((-116506335599/2199023255552), (3870590151/549755813888)), (1/2199023255552), by norm_num⟩
  | 21 => ⟨((30504410649/549755813888), (-2022011829/274877906944)), (1/1099511627776), by norm_num⟩
  | 20 => ⟨((-64038207861/1099511627776), (4233739835/549755813888)), (1/1099511627776), by norm_num⟩
  | 19 => ⟨((33692129549/549755813888), (-4442146385/549755813888)), (1/1099511627776), by norm_num⟩
  | 18 => ⟨((-8887422835/137438953472), (9344301405/1099511627776)), (1/1099511627776), by norm_num⟩
  | 17 => ⟨((75248230519/1099511627776), (-76989011/8589934592)), (1/1099511627776), by norm_num⟩
  | 16 => ⟨((-39955748967/549755813888), (10423898555/1099511627776)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((85191231641/1099511627776), (-11063093735/1099511627776)), (1/1099511627776), by norm_num⟩
  | 14 => ⟨((-22804598889/274877906944), (5892953545/549755813888)), (1/549755813888), by norm_num⟩
  | 13 => ⟨((49081950503/549755813888), (-6304959521/549755813888)), (1/549755813888), by norm_num⟩
  | 12 => ⟨((-106255106259/1099511627776), (6779008757/549755813888)), (1/549755813888), by norm_num⟩
  | 11 => ⟨((28950309189/274877906944), (-1832570975/137438953472)), (1/1099511627776), by norm_num⟩
  | 10 => ⟨((-63616957719/549755813888), (7979371883/549755813888)), (1/549755813888), by norm_num⟩
  | 9 => ⟨((70587222657/549755813888), (-4377454521/274877906944)), (1/549755813888), by norm_num⟩
  | 8 => ⟨((-79275509507/549755813888), (9697952495/549755813888)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((45203812455/274877906944), (-5434778239/274877906944)), (1/549755813888), by norm_num⟩
  | 6 => ⟨((-52593143007/274877906944), (12364686849/549755813888)), (1/274877906944), by norm_num⟩
  | 5 => ⟨((491254345/2147483648), (-7169845591/274877906944)), (1/274877906944), by norm_num⟩
  | 4 => ⟨((-78196651971/274877906944), (2133976737/68719476736)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((103456055977/274877906944), (-10552637799/274877906944)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((-76588560605/137438953472), (3459973501/68719476736)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((37298586643/34359738368), (-2524826681/34359738368)), (1/68719476736), by norm_num⟩
  | 0 => ⟨((-46590328737/274877906944), (38237550715/274877906944)), (1/137438953472), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (2397/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (2397/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (2397/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((44720816003/17179869184), (4779693839/34359738368)), (1/34359738368), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (2397/1280))) (z:=((-21/128), (2397/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((44720816003/17179869184), (4779693839/34359738368))) (r:=(1/34359738368)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((35706571517/1073741824), (14314499335/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((61270794995/34359738368), (2478038905/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((848007068851200/89305350979120081), (-123015424123680/89305350979120081)), 0, by norm_num⟩
  | 3 => ⟨((-33089867727/281474976710656), (19588981287/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((38411520765/18014398509481984), (-35343889583/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-26067780451/576460752303423488), (16868510621/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((19073769997/18446744073709551616), (-16635553579/18446744073709551616)), (39/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-28818672129/1180591620717411303424), (2091672857/73786976294838206464)), (27/590295810358705651712), by norm_num⟩
  | 8 => ⟨((21761992043/37778931862957161709568), (-8516827095/9444732965739290427392)), (131/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-15849826993/1208925819614629174706176), (69819553735/2417851639229258349412352)), (81/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((20949854673/77371252455336267181195264), (-71744940281/77371252455336267181195264)), (215/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-10549733823/2475880078570760549798248448), (73700469191/2475880078570760549798248448)), (69/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((30003703/79228162514264337593543950336), (-75482595103/79228162514264337593543950336)), (345/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21345274621/1073741824), (2573250165/536870912)), (5/4294967296), by norm_num⟩
  | 1 => ⟨((44090925811/34359738368), (2478038905/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((848007068851200/89305350979120081), (-123015424123680/89305350979120081)), 0, by norm_num⟩
  | 3 => ⟨((-33089867727/281474976710656), (19588981287/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((38411520765/18014398509481984), (-35343889583/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-26067780451/576460752303423488), (16868510621/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((19073769997/18446744073709551616), (-16635553579/18446744073709551616)), (39/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-28818672129/1180591620717411303424), (2091672857/73786976294838206464)), (27/590295810358705651712), by norm_num⟩
  | 8 => ⟨((21761992043/37778931862957161709568), (-8516827095/9444732965739290427392)), (131/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-15849826993/1208925819614629174706176), (69819553735/2417851639229258349412352)), (81/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((20949854673/77371252455336267181195264), (-71744940281/77371252455336267181195264)), (215/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-10549733823/2475880078570760549798248448), (73700469191/2475880078570760549798248448)), (69/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((30003703/79228162514264337593543950336), (-75482595103/79228162514264337593543950336)), (345/79228162514264337593543950336), by norm_num⟩
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
  | 0 => ⟨((89327909431/4294967296), (2573250165/536870912)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((44090925811/34359738368), (2478038905/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((848007068851200/89305350979120081), (-123015424123680/89305350979120081)), 0, by norm_num⟩
  | 3 => ⟨((-33089867727/281474976710656), (19588981287/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((38411520765/18014398509481984), (-35343889583/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-26067780451/576460752303423488), (16868510621/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((19073769997/18446744073709551616), (-16635553579/18446744073709551616)), (39/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-28818672129/1180591620717411303424), (2091672857/73786976294838206464)), (27/590295810358705651712), by norm_num⟩
  | 8 => ⟨((21761992043/37778931862957161709568), (-8516827095/9444732965739290427392)), (131/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-15849826993/1208925819614629174706176), (69819553735/2417851639229258349412352)), (81/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((20949854673/77371252455336267181195264), (-71744940281/77371252455336267181195264)), (215/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-10549733823/2475880078570760549798248448), (73700469191/2475880078570760549798248448)), (69/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((30003703/79228162514264337593543950336), (-75482595103/79228162514264337593543950336)), (345/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((470792259174400/89305350979120081), (-134468861952000/89305350979120081)), 0, by norm_num⟩
  | 1 => ⟨((-26114526655/70368744177664), (11578255255/70368744177664)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((1347056959/70368744177664), (-6702813353/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-7695020879/9007199254740992), (51383509359/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((9966470455/288230376151711744), (-43999266269/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((-11863603429/9223372036854775808), (69805735835/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 6 => ⟨((12894420523/295147905179352825856), (-13080632439/147573952589676412928)), (7/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-6189149543/4722366482869645213696), (37499642173/9444732965739290427392)), (11/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((18816539849/604462909807314587353088), (-51784075857/302231454903657293676544)), (9/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-1406541805/4835703278458516698824704), (69224204233/9671406556917033397649408)), (7/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-8878102263/309485009821345068724781056), (-22462062819/77371252455336267181195264)), (11/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((6866112287/2475880078570760549798248448), (56703884619/4951760157141521099596496896)), (17/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-27545119733/158456325028528675187087900672), (-69628769553/158456325028528675187087900672)), (25/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((26114526655/70368744177664), (-11578255255/70368744177664)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-1347056959/35184372088832), (6702813353/281474976710656)), (1/562949953421312), by norm_num⟩
  | 2 => ⟨((23085062637/9007199254740992), (-38537632019/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 3 => ⟨((-39865881821/288230376151711744), (10999816567/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((29659008573/4611686018427387904), (-43628584897/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-302212981/1152921504606846976), (78483794635/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 6 => ⟨((2707752925/295147905179352825856), (-65624373803/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-18816539849/75557863725914323419136), (51784075857/37778931862957161709568)), (1/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((3164719061/1208925819614629174706176), (-77877229763/1208925819614629174706176)), (15/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((11097627829/38685626227668133590597632), (112310314095/38685626227668133590597632)), (25/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-9440904395/309485009821345068724781056), (-77967841351/618970019642690137449562112)), (21/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((2582354975/1237940039285380274899124224), (52221577165/9903520314283042199192993792)), (9/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-19143067921/158456325028528675187087900672), (-67521944087/316912650057057350374175801344)), (27/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((28737215125/1125899906842624), (-35748337883/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-61560167033/18014398509481984), (25691754679/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((39865881821/144115188075855872), (-10999816567/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((-9886336191/576460752303423488), (58171446529/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 4 => ⟨((8059012827/9223372036854775808), (-65403162195/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-2707752925/73786976294838206464), (65624373803/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 6 => ⟨((343009841/295147905179352825856), (-60414755167/9444732965739290427392)), (9/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-4219625415/302231454903657293676544), (51918153175/151115727451828646838272)), (9/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-1040402609/604462909807314587353088), (-84232735571/4835703278458516698824704)), (9/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((7867420329/38685626227668133590597632), (32486600563/38685626227668133590597632)), (17/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-18937269817/1237940039285380274899124224), (-95739558135/2475880078570760549798248448)), (29/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((19143067921/19807040628566084398385987584), (67521944087/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-35007199935/633825300114114700748351602688), (-5697784945/79228162514264337593543950336)), (11/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7695020879/4503599627370496), (-51383509359/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((-39865881821/144115188075855872), (10999816567/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((29659008573/1152921504606846976), (-681696639/18014398509481984)), (5/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-8059012827/4611686018427387904), (65403162195/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((27077529251/295147905179352825856), (-82030467253/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-1029029523/295147905179352825856), (45311066375/2361183241434822606848)), (13/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((1846086119/37778931862957161709568), (-90856768057/75557863725914323419136)), (1/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((1040402609/151115727451828646838272), (84232735571/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-17701695741/19342813113834066795298816), (-73094851267/19342813113834066795298816)), (9/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((23671587271/309485009821345068724781056), (59837223835/309485009821345068724781056)), (9/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((-26321718391/4951760157141521099596496896), (-2901333535/309485009821345068724781056)), (17/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((26255399951/79228162514264337593543950336), (68373419341/158456325028528675187087900672)), (31/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-24280216197/1267650600228229401496703205376), (-47729306597/2535301200456458802993406410752)), (7/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((63785410913/576460752303423488), (-35199413015/288230376151711744)), (7/576460752303423488), by norm_num⟩
  | 1 => ⟨((-47454413717/2305843009213693952), (34902867917/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 2 => ⟨((38683261569/18446744073709551616), (-78483794633/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-21662023401/147573952589676412928), (32812186901/73786976294838206464)), (9/147573952589676412928), by norm_num⟩
  | 4 => ⟨((16464472369/2361183241434822606848), (-45311066375/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-2215303343/18889465931478580854784), (109028121667/37778931862957161709568)), (19/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-2913127305/151115727451828646838272), (-14740728725/75557863725914323419136)), (23/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((885084787/302231454903657293676544), (58475881013/4835703278458516698824704)), (15/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-10402553/37778931862957161709568), (-53853501451/77371252455336267181195264)), (1/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((26321718391/1237940039285380274899124224), (2901333535/77371252455336267181195264)), (17/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-14440469973/9903520314283042199192993792), (-75210761275/39614081257132168796771975168)), (33/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((7284064859/79228162514264337593543950336), (57275167917/633825300114114700748351602688)), (1/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-27546212115/5070602400912917605986812821504), (-40818646517/10141204801825835211973625643008)), (31/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((31636275811/4611686018427387904), (-46537157223/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-12894420523/9223372036854775808), (13080632439/4611686018427387904)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((21662023401/147573952589676412928), (-32812186901/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-10976314913/1180591620717411303424), (30207377583/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 4 => ⟨((3692172239/18889465931478580854784), (-11357096007/2361183241434822606848)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((2913127305/75557863725914323419136), (117925829799/302231454903657293676544)), (3/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-16521582691/2417851639229258349412352), (-34110930591/1208925819614629174706176)), (1/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((28405904725/38685626227668133590597632), (71804668601/38685626227668133590597632)), (21/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-19741288793/309485009821345068724781056), (-8704000605/77371252455336267181195264)), (25/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((24067449955/4951760157141521099596496896), (15668908599/2475880078570760549798248448)), (7/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-53416475633/158456325028528675187087900672), (-52502237257/158456325028528675187087900672)), (15/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((55092424229/2535301200456458802993406410752), (40818646517/2535301200456458802993406410752)), (15/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-53507352937/40564819207303340847894502572032), (-29130682565/40564819207303340847894502572032)), (15/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((29472961195/73786976294838206464), (-1868661777/2305843009213693952)), (9/73786976294838206464), by norm_num⟩
  | 1 => ⟨((-6189149543/73786976294838206464), (74999284345/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 2 => ⟨((9408269925/1180591620717411303424), (-103568151713/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-4219625417/18889465931478580854784), (103836306349/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((-8323220871/151115727451828646838272), (-84232735571/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((885084787/75557863725914323419136), (58475881013/1208925819614629174706176)), (7/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-28405904725/19342813113834066795298816), (-71804668601/19342813113834066795298816)), (21/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((45122945813/309485009821345068724781056), (79579434103/309485009821345068724781056)), (7/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-7735966057/618970019642690137449562112), (-20145739627/1237940039285380274899124224)), (9/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((9538656363/9903520314283042199192993792), (37501598041/39614081257132168796771975168)), (21/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-2705431547/39614081257132168796771975168), (-8017948423/158456325028528675187087900672)), (3/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((22931722687/5070602400912917605986812821504), (6242289121/2535301200456458802993406410752)), (13/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((-45846624931/162259276829213363391578010288128), (-17227739321/162259276829213363391578010288128)), (27/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6189149543/295147905179352825856), (-74999284345/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-9408269925/2361183241434822606848), (103568151713/4722366482869645213696)), (1/295147905179352825856), by norm_num⟩
  | 2 => ⟨((1582359531/9444732965739290427392), (-38938614881/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((4161610435/75557863725914323419136), (84232735571/151115727451828646838272)), (19/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-17701695739/1208925819614629174706176), (-36547425633/604462909807314587353088)), (19/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((10402553/4722366482869645213696), (53853501451/9671406556917033397649408)), (1/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-19741288793/77371252455336267181195264), (-8704000605/19342813113834066795298816)), (25/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((7735966057/309485009821345068724781056), (20145739627/618970019642690137449562112)), (9/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-42923953633/19807040628566084398385987584), (-10547324449/4951760157141521099596496896)), (3/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((13527157735/79228162514264337593543950336), (40089742115/316912650057057350374175801344)), (15/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-31531118695/2535301200456458802993406410752), (-17166295083/2535301200456458802993406410752)), (9/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((68769937397/81129638414606681695789005144064), (25841608981/81129638414606681695789005144064)), (41/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-8846891555/162259276829213363391578010288128), (-3962940043/324518553658426726783156020576256)), (45/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1045363325/1180591620717411303424), (-92060579301/18889465931478580854784)), (19/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((-2813083611/37778931862957161709568), (69224204233/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-2774406957/75557863725914323419136), (-56155157047/151115727451828646838272)), (27/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((15734840657/1208925819614629174706176), (32486600563/604462909807314587353088)), (9/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((-11835793635/4835703278458516698824704), (-29918611917/4835703278458516698824704)), (19/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((26321718391/77371252455336267181195264), (2901333535/4835703278458516698824704)), (9/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-48134899909/1237940039285380274899124224), (-15668908599/309485009821345068724781056)), (29/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((9538656363/2475880078570760549798248448), (37501598041/9903520314283042199192993792)), (11/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-54108630939/158456325028528675187087900672), (-40089742115/158456325028528675187087900672)), (31/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((70069152655/2535301200456458802993406410752), (38147322407/2535301200456458802993406410752)), (5/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-84052145707/40564819207303340847894502572032), (-31584188755/40564819207303340847894502572032)), (51/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((94366843253/649037107316853453566312041152512), (10567840115/324518553658426726783156020576256)), (61/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-49957682657/5192296858534827628530496329220096), (-8134010459/10384593717069655257060992658440192)), (69/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4500933777/302231454903657293676544), (-110758726773/302231454903657293676544)), (13/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((4439051131/302231454903657293676544), (22462062819/151115727451828646838272)), (21/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-18881808789/2417851639229258349412352), (-77967841351/2417851639229258349412352)), (11/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((2367158727/1208925819614629174706176), (95739558135/19342813113834066795298816)), (1/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((-13160859195/38685626227668133590597632), (-2901333535/4835703278458516698824704)), (9/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((57761879891/1237940039285380274899124224), (75210761275/1237940039285380274899124224)), (37/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-3338529727/618970019642690137449562112), (-26251118629/4951760157141521099596496896)), (1/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((43286904751/79228162514264337593543950336), (8017948423/19807040628566084398385987584)), (13/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((-63062237389/1267650600228229401496703205376), (-17166295083/633825300114114700748351602688)), (37/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((84052145707/20282409603651670423947251286016), (31584188755/20282409603651670423947251286016)), (13/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((-51901763789/162259276829213363391578010288128), (-23249248253/324518553658426726783156020576256)), (17/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((14987304797/649037107316853453566312041152512), (9760812551/5192296858534827628530496329220096)), (85/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((-32604844077/20769187434139310514121985316880384), (472299421/5192296858534827628530496329220096)), (51/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/896520027), (-255680/298840009)), 0, by norm_num⟩
  | 1 => ⟨((-58849032396800/267916052937360243), (5602869248000/89305350979120081)), 0, by norm_num⟩
  | 2 => ⟨((69638737747/9007199254740992), (-30875347347/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-76632573667/288230376151711744), (47664450511/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((41040111355/4611686018427387904), (-17127836453/2305843009213693952)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-42523607275/147573952589676412928), (46932550687/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 6 => ⟨((42181701081/4722366482869645213696), (-15512385741/1180591620717411303424)), (9/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-39297281593/151115727451828646838272), (622887259/1180591620717411303424)), (13/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((33008797563/4835703278458516698824704), (-99999045793/4835703278458516698824704)), (9/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-11150542133/77371252455336267181195264), (30686859767/38685626227668133590597632)), (13/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((1500311259/1237940039285380274899124224), (-36919575591/1237940039285380274899124224)), (9/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((2152267215/19807040628566084398385987584), (87125576995/79228162514264337593543950336)), (25/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-24412843687/2535301200456458802993406410752), (-100806905989/2535301200456458802993406410752)), (17/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11169269357/536870912), (10291163327/2147483648)), (7/4294967296), by norm_num⟩
  | 1 => ⟨((88166757063/68719476736), (1240097289/17179869184)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((2612253329/274877906944), (-12146504219/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-66329408449/562949953421312), (19682075917/562949953421312)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((9642958425/4503599627370496), (-8902878007/9007199254740992)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-6558472073/144115188075855872), (17051840897/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((19238542267/18446744073709551616), (-8438967303/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-58251364283/2361183241434822606848), (34089652971/1180591620717411303424)), (109/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((11009936637/18889465931478580854784), (-69697101851/75557863725914323419136)), (33/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-8012027107/604462909807314587353088), (35868741235/1208925819614629174706176)), (41/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((21043624127/77371252455336267181195264), (-74052413755/77371252455336267181195264)), (217/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-10280700421/2475880078570760549798248448), (4776446467/154742504910672534362390528)), (277/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-366448831/39614081257132168796771975168), (-78632810915/79228162514264337593543950336)), (347/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-74281320263/72057594037927936), (8233425959/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 1 => ⟨((30653029467/288230376151711744), (-4766445051/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((-65664178167/9223372036854775808), (54809076649/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 3 => ⟨((28349071517/73786976294838206464), (-7822091781/18446744073709551616)), (7/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-21090850541/1180591620717411303424), (62049542965/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((27508097115/37778931862957161709568), (-55810698407/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-15404105529/604462909807314587353088), (46666221371/604462909807314587353088)), (7/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((13380650559/19342813113834066795298816), (-73648463441/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-281308361/38685626227668133590597632), (55379363387/309485009821345068724781056)), (11/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-986455807/1237940039285380274899124224), (-79865112245/9903520314283042199192993792)), (19/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((3356766007/39614081257132168796771975168), (27721899147/79228162514264337593543950336)), (1/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-29381461049/5070602400912917605986812821504), (-18567671881/1267650600228229401496703205376)), (27/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((27225696599/81129638414606681695789005144064), (12003901171/20282409603651670423947251286016)), (5/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22338537607/1073741824), (20582328617/4294967296)), (1/536870912), by norm_num⟩
  | 1 => ⟨((88166764371/68719476736), (2480192305/34359738368)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((41796021953/4398046511104), (-12146451949/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-66329192163/562949953421312), (9840918603/281474976710656)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((38571511879/18014398509481984), (-35610565227/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-52466937103/1152921504606846976), (34101978587/1152921504606846976)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((19238072171/18446744073709551616), (-8438255233/9223372036854775808)), (41/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-58249730903/2361183241434822606848), (68170315651/2361183241434822606848)), (55/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((22019598559/37778931862957161709568), (-69683581499/75557863725914323419136)), (133/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-32050035099/2417851639229258349412352), (8964748019/302231454903657293676544)), (165/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((21050180311/77371252455336267181195264), (-18506335397/19342813113834066795298816)), (109/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-5147523419/1237940039285380274899124224), (9548359811/309485009821345068724781056)), (139/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-176577517/19807040628566084398385987584), (-19646480169/19807040628566084398385987584)), (87/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3126865627/2305843009213693952), (-41759296495/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-64797877753/295147905179352825856), (1117441683/4611686018427387904)), (1/36893488147419103232), by norm_num⟩
  | 2 => ⟨((48207658379/2361183241434822606848), (-70913763387/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-13099093865/9444732965739290427392), (53153046101/18889465931478580854784)), (1/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((11002932521/151115727451828646838272), (-66666030529/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-13380650559/4835703278458516698824704), (73648463441/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((3000622517/77371252455336267181195264), (-73839151183/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((6764268391/1237940039285380274899124224), (1069622039/19342813113834066795298816)), (15/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-14386140031/19807040628566084398385987584), (-59404069601/19807040628566084398385987584)), (15/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((19237861401/316912650057057350374175801344), (48629616831/316912650057057350374175801344)), (15/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-5347904689/1267650600228229401496703205376), (-75453093075/10141204801825835211973625643008)), (29/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((21337721865/81129638414606681695789005144064), (55566969369/162259276829213363391578010288128)), (13/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-39464986327/2596148429267413814265248164610048), (-38789531711/2596148429267413814265248164610048)), (3/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44677075217/2147483648), (5145582153/1073741824)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((22041691089/17179869184), (4960384627/68719476736)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((41796022043/4398046511104), (-12146452213/8796093022208)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-4145574559/35184372088832), (9840919395/281474976710656)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((77143026381/36028797018963968), (-17805286587/18014398509481984)), (19/36028797018963968), by norm_num⟩
  | 5 => ⟨((-52466940293/1152921504606846976), (17050998073/576460752303423488)), (27/1152921504606846976), by norm_num⟩
  | 6 => ⟨((38476145773/36893488147419103232), (-33753056141/36893488147419103232)), (21/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-58249718001/2361183241434822606848), (17042611555/590295810358705651712)), (111/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((44039142239/75557863725914323419136), (-17420952027/18889465931478580854784)), (67/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-16024944163/1208925819614629174706176), (71718355167/2417851639229258349412352)), (83/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((21049853901/77371252455336267181195264), (-74025917249/77371252455336267181195264)), (219/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-5147197831/1237940039285380274899124224), (76387726373/2475880078570760549798248448)), (279/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-176878611/19807040628566084398385987584), (-78587104439/79228162514264337593543950336)), (349/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-38566126703/9444732965739290427392), (28365505355/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((31437825275/37778931862957161709568), (-31891827661/18889465931478580854784)), (1/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((-26407038051/302231454903657293676544), (79999236635/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((13380650561/2417851639229258349412352), (-4603028965/151115727451828646838272)), (7/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((-4500933777/38685626227668133590597632), (110758726773/38685626227668133590597632)), (5/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-3551240905/154742504910672534362390528), (-17969650255/77371252455336267181195264)), (1/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((10070298021/2475880078570760549798248448), (83165697441/4951760157141521099596496896)), (5/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-17314075261/39614081257132168796771975168), (-87533310295/79228162514264337593543950336)), (27/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((6016392775/158456325028528675187087900672), (42442364855/633825300114114700748351602688)), (31/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((-7334841891/2535301200456458802993406410752), (-76404582883/20282409603651670423947251286016)), (35/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((32558613719/162259276829213363391578010288128), (64002727323/324518553658426726783156020576256)), (19/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((-8395036073/649037107316853453566312041152512), (-49759873849/5192296858534827628530496329220096)), (37/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((65228011199/83076749736557242056487941267521536), (17755844611/41538374868278621028243970633760768)), (19/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44677075217/2147483648), (5145582153/1073741824)), (5/2147483648), by norm_num⟩
  | 1 => ⟨((22041691089/17179869184), (4960384627/68719476736)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((83592044085/8796093022208), (-12146452211/8796093022208)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-66329192941/562949953421312), (19681838773/562949953421312)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((77143026377/36028797018963968), (-35610573071/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-52466940319/1152921504606846976), (17050997939/576460752303423488)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((38476145923/36893488147419103232), (-33753055521/36893488147419103232)), (43/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-58249719033/2361183241434822606848), (68170443611/2361183241434822606848)), (7/147573952589676412928), by norm_num⟩
  | 8 => ⟨((11009786277/18889465931478580854784), (-8710475381/9444732965739290427392)), (135/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-32049895321/2417851639229258349412352), (71718346059/2417851639229258349412352)), (167/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((10524934713/38685626227668133590597632), (-37012950995/38685626227668133590597632)), (55/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-10294427687/2475880078570760549798248448), (38193851323/1237940039285380274899124224)), (35/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-353726119/39614081257132168796771975168), (-19646767643/19807040628566084398385987584)), (175/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21339020647/1208925819614629174706176), (-32322923893/604462909807314587353088)), (13/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((-2027371297/604462909807314587353088), (11158858097/604462909807314587353088)), (15/4835703278458516698824704), by norm_num⟩
  | 2 => ⟨((2727838653/19342813113834066795298816), (-33563250537/9671406556917033397649408)), (15/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((3587112025/77371252455336267181195264), (9075580937/19342813113834066795298816)), (9/77371252455336267181195264), by norm_num⟩
  | 4 => ⟨((-1907253413/154742504910672534362390528), (-63004316243/1237940039285380274899124224)), (17/1237940039285380274899124224), by norm_num⟩
  | 5 => ⟨((4590853289/2475880078570760549798248448), (23209589851/4951760157141521099596496896)), (29/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((-8508030187/39614081257132168796771975168), (-60019505855/158456325028528675187087900672)), (23/158456325028528675187087900672), by norm_num⟩
  | 7 => ⟨((26672152331/1267650600228229401496703205376), (69458711711/2535301200456458802993406410752)), (1/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((-4624803085/2535301200456458802993406410752), (-36365185979/20282409603651670423947251286016)), (11/10141204801825835211973625643008), by norm_num⟩
  | 9 => ⟨((46639089295/324518553658426726783156020576256), (34555467951/324518553658426726783156020576256)), (13/162259276829213363391578010288128), by norm_num⟩
  | 10 => ⟨((-54356675999/5192296858534827628530496329220096), (-1849567147/324518553658426726783156020576256)), (1/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((14819111089/20769187434139310514121985316880384), (22274248819/83076749736557242056487941267521536)), (37/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((-30502413981/664613997892457936451903530140172288), (-13663470047/1329227995784915872903807060280344576)), (5/166153499473114484112975882535043072), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44677075217/2147483648), (5145582153/1073741824)), (11/4294967296), by norm_num⟩
  | 1 => ⟨((22041691089/17179869184), (4960384627/68719476736)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((83592044085/8796093022208), (-12146452211/8796093022208)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((-66329192941/562949953421312), (19681838773/562949953421312)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((77143026377/36028797018963968), (-35610573073/36028797018963968)), (21/36028797018963968), by norm_num⟩
  | 5 => ⟨((-52466940317/1152921504606846976), (34101995883/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 6 => ⟨((38476145915/36893488147419103232), (-33753055535/36893488147419103232)), (11/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-58249718983/2361183241434822606848), (17042610919/590295810358705651712)), (113/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((22019572485/37778931862957161709568), (-69683803183/75557863725914323419136)), (17/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-16024947487/1208925819614629174706176), (17929586579/604462909807314587353088)), (21/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((2631233577/9671406556917033397649408), (-74025902431/77371252455336267181195264)), (221/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-160850405/38685626227668133590597632), (38193851655/1237940039285380274899124224)), (281/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-353727937/39614081257132168796771975168), (-39293535693/39614081257132168796771975168)), (351/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-552362347/19342813113834066795298816), (3398125439/4835703278458516698824704)), (27/154742504910672534362390528), by norm_num⟩
  | 1 => ⟨((-8716288033/309485009821345068724781056), (-88210657441/309485009821345068724781056)), (21/309485009821345068724781056), by norm_num⟩
  | 2 => ⟨((9268832411/618970019642690137449562112), (19136695615/309485009821345068724781056)), (23/1237940039285380274899124224), by norm_num⟩
  | 3 => ⟨((-37184230007/9903520314283042199192993792), (-11749323507/1237940039285380274899124224)), (33/9903520314283042199192993792), by norm_num⟩
  | 4 => ⟨((25841973007/39614081257132168796771975168), (22787625575/19807040628566084398385987584)), (19/39614081257132168796771975168), by norm_num⟩
  | 5 => ⟨((-56709099263/633825300114114700748351602688), (-73839953527/633825300114114700748351602688)), (37/633825300114114700748351602688), by norm_num⟩
  | 6 => ⟨((26221447645/2535301200456458802993406410752), (6443165003/633825300114114700748351602688)), (33/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((-42497948179/40564819207303340847894502572032), (-31487246181/40564819207303340847894502572032)), (27/40564819207303340847894502572032), by norm_num⟩
  | 8 => ⟨((61912851289/649037107316853453566312041152512), (33706836885/649037107316853453566312041152512)), (19/324518553658426726783156020576256), by norm_num⟩
  | 9 => ⟨((-82520192957/10384593717069655257060992658440192), (-15504264219/5192296858534827628530496329220096)), (13/2596148429267413814265248164610048), by norm_num⟩
  | 10 => ⟨((12738947729/20769187434139310514121985316880384), (22825502381/166153499473114484112975882535043072)), (17/41538374868278621028243970633760768), by norm_num⟩
  | 11 => ⟨((-117713143273/2658455991569831745807614120560689152), (-9582909851/2658455991569831745807614120560689152)), (85/2658455991569831745807614120560689152), by norm_num⟩
  | 12 => ⟨((64021162147/21267647932558653966460912964485513216), (-7419059019/42535295865117307932921825928971026432)), (101/42535295865117307932921825928971026432), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44677075217/2147483648), (5145582153/1073741824)), (3/1073741824), by norm_num⟩
  | 1 => ⟨((22041691089/17179869184), (4960384627/68719476736)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((83592044085/8796093022208), (-12146452211/8796093022208)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-66329192941/562949953421312), (19681838773/562949953421312)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((77143026377/36028797018963968), (-35610573073/36028797018963968)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-52466940317/1152921504606846976), (34101995883/1152921504606846976)), (15/576460752303423488), by norm_num⟩
  | 6 => ⟨((38476145915/36893488147419103232), (-33753055535/36893488147419103232)), (45/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-58249718985/2361183241434822606848), (34085221837/1180591620717411303424)), (57/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((44039144977/75557863725914323419136), (-69683803179/75557863725914323419136)), (137/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-32049894993/2417851639229258349412352), (71718346309/2417851639229258349412352)), (169/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((21049868663/77371252455336267181195264), (-18506475605/19342813113834066795298816)), (111/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-5147213015/1237940039285380274899124224), (76387703301/2475880078570760549798248448)), (141/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-176863909/19807040628566084398385987584), (-9823383925/9903520314283042199192993792)), (11/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((90659571969583/1048576), (-1133560476200925/1048576)), (8095935/1048576), by norm_num⟩
  | 1 => ⟨((6046744029/32), (-44183613675/32)), (679/64), by norm_num⟩
  | 2 => ⟨((10904300139/64), (-56916042437/64)), (59/8), by norm_num⟩
  | 3 => ⟨((6029882649/64), (-98565112525/256)), (221/64), by norm_num⟩
  | 4 => ⟨((19139653139/512), (-32259396023/256)), (629/512), by norm_num⟩
  | 5 => ⟨((11840283939/1024), (-68089569745/2048)), (181/512), by norm_num⟩
  | 6 => ⟨((24033302121/8192), (-15080528483/2048)), (701/8192), by norm_num⟩
  | 7 => ⟨((41407868099/65536), (-46130098993/32768)), (147/8192), by norm_num⟩
  | 8 => ⟨((31029196303/262144), (-62154064207/262144)), (873/262144), by norm_num⟩
  | 9 => ⟨((10300018917/524288), (-18731256525/524288)), (291/524288), by norm_num⟩
  | 10 => ⟨((49159630779/16777216), (-81797830627/16777216)), (353/4194304), by norm_num⟩
  | 11 => ⟨((26655769009/67108864), (-40836054889/67108864)), (787/67108864), by norm_num⟩
  | 12 => ⟨((53032531865/1073741824), (-75184100237/1073741824)), (813/536870912), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1611075800554161/10141204801825835211973625643008), (-1942178976069/10141204801825835211973625643008)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1814701785277951/633825300114114700748351602688), (-2385255186253/633825300114114700748351602688)), (4481/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((120638216307757/2475880078570760549798248448), (-2690745349309/39614081257132168796771975168)), (5057/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((966278900484993/1237940039285380274899124224), (-1432569516195/1237940039285380274899124224)), (5385/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((907135544995547/77371252455336267181195264), (-2872098523807/154742504910672534362390528)), (5399/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1589991386211377/9671406556917033397649408), (-1350004664011/4835703278458516698824704)), (5077/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1294222104031801/604462909807314587353088), (-1184976018345/302231454903657293676544)), (4457/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((972732872793767/37778931862957161709568), (-3865186819969/75557863725914323419136)), (7271/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((670438790697453/2361183241434822606848), (-2911210804457/4722366482869645213696)), (2739/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((840586582256323/295147905179352825856), (-1005761224093/147573952589676412928)), (7573/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1898334474871605/73786976294838206464), (-1264798246029/18446744073709551616)), (9527/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1907155495347531/9223372036854775808), (-2866843989103/4611686018427387904)), (10803/9223372036854775808), by norm_num⟩
  | 6 => ⟨((839378846932715/576460752303423488), (-5786782691277/1152921504606846976)), (5455/576460752303423488), by norm_num⟩
  | 5 => ⟨((1269156955870239/144115188075855872), (-2561912937433/72057594037927936)), (9669/144115188075855872), by norm_num⟩
  | 4 => ⟨((200538846561679/4503599627370496), (-3904094637219/18014398509481984)), (7375/18014398509481984), by norm_num⟩
  | 3 => ⟨((815766062936919/4503599627370496), (-9978333846323/9007199254740992)), (295/140737488355328), by norm_num⟩
  | 2 => ⟨((1258431718793151/2251799813685248), (-5156618576131/1125899906842624)), (19561/2251799813685248), by norm_num⟩
  | 1 => ⟨((20786219277945/17592186044416), (-16334904344121/1125899906842624)), (15551/562949953421312), by norm_num⟩
  | 0 => ⟨((778981926389261/562949953421312), (-18150988304137/562949953421312)), (69625/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((778981926389261/562949953421312), (-18150988304137/562949953421312)), (265598301414107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((538665452922433/281474976710656), (-784888367357/8796093022208)), (98589/562949953421312), by norm_num⟩
  | 2 => ⟨((514307947747981/140737488355328), (-192263654705997/562949953421312)), (98735/140737488355328), by norm_num⟩
  | 3 => ⟨((931529815272765/70368744177664), (-351302012114615/140737488355328)), (789073/140737488355328), by norm_num⟩
  | 4 => ⟨((1486623305903065/8796093022208), (-290654876566945/4398046511104)), (1551909/8796093022208), by norm_num⟩
  | 5 => ⟨((415695883174821/17179869184), (-767553689014021/34359738368)), (1425191/17179869184), by norm_num⟩
  | 6 => ⟨((90659571969583/1048576), (-1133560476200925/1048576)), (8095935/1048576), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((44677075217/2147483648), (5145582153/1073741824)), (3/1073741824), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/8843209), (-3068160/8843209)), 0, by norm_num⟩
  | 1 => ⟨((2169248972800/78202345417681), (6911950848000/78202345417681)), 0, by norm_num⟩
  | 2 => ⟨((-82973307541/4398046511104), (-28349974703/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((61946862415/17592186044416), (-21565538059/8796093022208)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((-3266166907/140737488355328), (32480129517/35184372088832)), (3/70368744177664), by norm_num⟩
  | 5 => ⟨((-44243997389/281474976710656), (-534849089/4398046511104)), (1/70368744177664), by norm_num⟩
  | 6 => ⟨((92589485331/2251799813685248), (-13260695129/1125899906842624)), (11/2251799813685248), by norm_num⟩
  | 7 => ⟨((-28770941367/9007199254740992), (77760628135/9007199254740992)), (15/9007199254740992), by norm_num⟩
  | 8 => ⟨((-19649752947/18014398509481984), (-59583120681/36028797018963968)), (19/36028797018963968), by norm_num⟩
  | 9 => ⟨((61367875491/144115188075855872), (6174990217/288230376151711744)), (47/288230376151711744), by norm_num⟩
  | 10 => ⟨((-33409247457/576460752303423488), (41010215157/576460752303423488)), (29/576460752303423488), by norm_num⟩
  | 11 => ⟨((-22870226889/4611686018427387904), (-88154754403/4611686018427387904)), (71/4611686018427387904), by norm_num⟩
  | 12 => ⟨((18205774533/4611686018427387904), (29045002869/18446744073709551616)), (43/9223372036854775808), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (2397/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (2397/1280)))⁻¹=value ((2252800/8843209), (-3068160/8843209)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/8843209), (-3068160/8843209))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/14987209), (-3068160/14987209)), 0, by norm_num⟩
  | 1 => ⟨((-2863915827200/224616433609681), (11938824192000/224616433609681)), 0, by norm_num⟩
  | 2 => ⟨((-8324187061/2199023255552), (-72173402053/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((11710114005/8796093022208), (23844518479/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-68171300015/281474976710656), (6796492027/140737488355328)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((14916900983/562949953421312), (-17485141857/562949953421312)), (1/281474976710656), by norm_num⟩
  | 6 => ⟨((-586824707/2251799813685248), (121496268359/18014398509481984)), (1/1125899906842624), by norm_num⟩
  | 7 => ⟨((-47307323509/72057594037927936), (-65011444917/72057594037927936)), (1/4503599627370496), by norm_num⟩
  | 8 => ⟨((51183348691/288230376151711744), (28778165905/576460752303423488)), (31/576460752303423488), by norm_num⟩
  | 9 => ⟨((-64938750151/2305843009213693952), (3371138133/288230376151711744)), (29/2305843009213693952), by norm_num⟩
  | 10 => ⟨((22678556787/9223372036854775808), (-81185137883/18446744073709551616)), (55/18446744073709551616), by norm_num⟩
  | 11 => ⟨((2421911655/18446744073709551616), (30363925005/36893488147419103232)), (13/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-29894736347/295147905179352825856), (-1722977241/18446744073709551616)), (49/295147905179352825856), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (2397/1280)))⁻¹=value ((3891200/14987209), (-3068160/14987209)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/14987209), (-3068160/14987209))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-647510425600/132535021513681), (-18850775040000/132535021513681)), 0, by norm_num⟩
  | 1 => ⟨((11129579779/274877906944), (1210610959/34359738368)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-33162466709/2199023255552), (7736726323/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((38526634405/17592186044416), (-27526667679/8796093022208)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((15409741551/70368744177664), (15390503255/17592186044416)), (5/70368744177664), by norm_num⟩
  | 5 => ⟨((-51702447881/281474976710656), (-1592985673/17592186044416)), (3/140737488355328), by norm_num⟩
  | 6 => ⟨((46588155019/1125899906842624), (-41708423803/2251799813685248)), (7/1125899906842624), by norm_num⟩
  | 7 => ⟨((-22857525929/9007199254740992), (42943529375/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 8 => ⟨((-1428044515/1125899906842624), (-30690878025/18014398509481984)), (23/36028797018963968), by norm_num⟩
  | 9 => ⟨((130853094751/288230376151711744), (2803852085/288230376151711744)), (27/144115188075855872), by norm_num⟩
  | 10 => ⟨((-34826657257/576460752303423488), (10886812679/144115188075855872)), (33/576460752303423488), by norm_num⟩
  | 11 => ⟨((-23475704803/4611686018427387904), (-45975122515/2305843009213693952)), (79/4611686018427387904), by norm_num⟩
  | 12 => ⟨((37345759577/9223372036854775808), (15383990055/9223372036854775808)), (47/9223372036854775808), by norm_num⟩
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
  | 0 => ⟨((27/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/2712001), (-1022720/8136003)), 0, by norm_num⟩
  | 1 => ⟨((-1175715020800/66194544816009), (209453056000/7354949424001)), 0, by norm_num⟩
  | 2 => ⟨((976575623/4398046511104), (-38193906855/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((34868840675/140737488355328), (35593170729/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-67391293867/1125899906842624), (-23488094545/562949953421312)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((84689802087/9007199254740992), (542775355/562949953421312)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-81112044125/72057594037927936), (34713289973/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 7 => ⟨((14012254397/144115188075855872), (-18060274295/144115188075855872)), (17/576460752303423488), by norm_num⟩
  | 8 => ⟨((-452112885/144115188075855872), (46823296793/2305843009213693952)), (25/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-33976163069/36893488147419103232), (-46068251885/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 10 => ⟨((9639543453/36893488147419103232), (16602489239/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-103274122745/2361183241434822606848), (-10702651319/1180591620717411303424)), (37/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((6521829397/1180591620717411303424), (-4066263065/2361183241434822606848)), (105/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (2397/1280)))⁻¹=value ((614400/2712001), (-1022720/8136003)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/2712001), (-1022720/8136003))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-20875175651/1099511627776), (-4344228019/137438953472)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((9752095499/549755813888), (23219931959/4398046511104)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-48699983673/8796093022208), (12363236961/4398046511104)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((19465011479/35184372088832), (-58077301915/35184372088832)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((220629771/1099511627776), (55227755189/140737488355328)), (3/70368744177664), by norm_num⟩
  | 5 => ⟨((-56514342057/562949953421312), (-8236906081/281474976710656)), (1/70368744177664), by norm_num⟩
  | 6 => ⟨((45614191683/2251799813685248), (-13952666759/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 7 => ⟨((-16068344591/18014398509481984), (46442361111/9007199254740992)), (23/18014398509481984), by norm_num⟩
  | 8 => ⟨((-52208371287/72057594037927936), (-62448777407/72057594037927936)), (15/36028797018963968), by norm_num⟩
  | 9 => ⟨((69352499873/288230376151711744), (-643551241/288230376151711744)), (35/288230376151711744), by norm_num⟩
  | 10 => ⟨((-18046724595/576460752303423488), (23106996611/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 11 => ⟨((-24282889987/9223372036854775808), (-11973442861/1152921504606846976)), (99/9223372036854775808), by norm_num⟩
  | 12 => ⟨((4791365235/2305843009213693952), (4057398709/4611686018427387904)), (59/18446744073709551616), by norm_num⟩
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
  | 0 => ⟨((35/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/37105609), (-3068160/37105609)), 0, by norm_num⟩
  | 1 => ⟨((-20983309107200/1376826219260881), (21992570880000/1376826219260881)), 0, by norm_num⟩
  | 2 => ⟨((7139393927/8796093022208), (-38226883099/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((402522495/35184372088832), (68522234209/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-25151930865/2251799813685248), (-51882975155/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((73190941993/36028797018963968), (31771694431/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((-77572526157/288230376151711744), (-24893001031/288230376151711744)), (5/144115188075855872), by norm_num⟩
  | 7 => ⟨((68174660875/2305843009213693952), (-1605468609/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((-50555443613/18446744073709551616), (13755481737/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((29965645585/147573952589676412928), (-75958494805/295147905179352825856)), (1/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-5296629943/590295810358705651712), (78516353803/2361183241434822606848)), (9/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-4799046007/9444732965739290427392), (-67678054449/18889465931478580854784)), (41/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((14900508605/75557863725914323419136), (24560589333/75557863725914323419136)), (47/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (2397/1280)))⁻¹=value ((7168000/37105609), (-3068160/37105609)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/37105609), (-3068160/37105609))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55250633871/8796093022208), (-1246893917/274877906944)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((81937059915/17592186044416), (-2361098763/8796093022208)), (3/17592186044416), by norm_num⟩
  | 2 => ⟨((-11222718423/8796093022208), (10725329623/8796093022208)), (5/35184372088832), by norm_num⟩
  | 3 => ⟨((6080976521/140737488355328), (-4707134619/8796093022208)), (7/140737488355328), by norm_num⟩
  | 4 => ⟨((6274253633/70368744177664), (63438438017/562949953421312)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((-39500989435/1125899906842624), (-640408217/140737488355328)), (7/1125899906842624), by norm_num⟩
  | 6 => ⟨((7279311723/1125899906842624), (-22877881129/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 7 => ⟨((-5779803081/36028797018963968), (65852469331/36028797018963968)), (21/36028797018963968), by norm_num⟩
  | 8 => ⟨((-19577868405/72057594037927936), (-41891944735/144115188075855872)), (13/72057594037927936), by norm_num⟩
  | 9 => ⟨((97488626211/1152921504606846976), (-2007898423/576460752303423488)), (31/576460752303423488), by norm_num⟩
  | 10 => ⟨((-49605934355/4611686018427387904), (65321698191/4611686018427387904)), (37/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-8429813053/9223372036854775808), (-66433416677/18446744073709551616)), (11/2305843009213693952), by norm_num⟩
  | 12 => ⟨((6560869511/9223372036854775808), (22741756877/73786976294838206464)), (103/73786976294838206464), by norm_num⟩
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
  | 0 => ⟨((43/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/53080009), (-3068160/53080009)), 0, by norm_num⟩
  | 1 => ⟨((-34069537587200/2817487355440081), (27019444224000/2817487355440081)), 0, by norm_num⟩
  | 2 => ⟨((25541516163/35184372088832), (-80572250661/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-15271215141/562949953421312), (32640626895/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-4959223169/4503599627370496), (-93707198101/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((14124130339/36028797018963968), (59893862417/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-8148631545/144115188075855872), (-66432411721/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((58621402197/9223372036854775808), (29014309149/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-22805725563/36893488147419103232), (-5700961409/73786976294838206464)), (19/147573952589676412928), by norm_num⟩
  | 9 => ⟨((3948418179/73786976294838206464), (-13524983891/1180591620717411303424)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-77595281953/18889465931478580854784), (47164495041/18889465931478580854784)), (33/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((40589810291/151115727451828646838272), (-49240696203/151115727451828646838272)), (15/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-31103502019/2417851639229258349412352), (21031243585/604462909807314587353088)), (55/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (2397/1280)))⁻¹=value ((8806400/53080009), (-3068160/53080009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/53080009), (-3068160/53080009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-91783047499/70368744177664), (-3426203377/8796093022208)), (5/70368744177664), by norm_num⟩
  | 1 => ⟨((30845095965/35184372088832), (-22457395363/70368744177664)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-28808607531/140737488355328), (11535408757/35184372088832)), (3/70368744177664), by norm_num⟩
  | 3 => ⟨((-4576459721/281474976710656), (-70027835139/562949953421312)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((59110646477/2251799813685248), (13168162827/562949953421312)), (13/2251799813685248), by norm_num⟩
  | 5 => ⟨((-20125111211/2251799813685248), (410998387/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 6 => ⟨((1708856145/1125899906842624), (-13352104515/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 7 => ⟨((-580443885/144115188075855872), (134925031/281474976710656)), (7/36028797018963968), by norm_num⟩
  | 8 => ⟨((-21732218793/288230376151711744), (-41737127439/576460752303423488)), (35/576460752303423488), by norm_num⟩
  | 9 => ⟨((102262540211/4611686018427387904), (-1889175009/1152921504606846976)), (41/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-50875810021/18446744073709551616), (17287120765/4611686018427387904)), (97/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-4415295055/18446744073709551616), (-69015314103/73786976294838206464)), (29/18446744073709551616), by norm_num⟩
  | 12 => ⟨((6741117929/36893488147419103232), (23815308417/295147905179352825856)), (17/36893488147419103232), by norm_num⟩
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
  | 0 => ⟨((51/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((204800/1418259), (-60160/1418259)), 0, by norm_num⟩
  | 1 => ⟨((-2129100800/223495399009), (12320768000/2011458591081)), 0, by norm_num⟩
  | 2 => ⟨((1591570595840000/2852769249927947979), (-1838036811776000/2852769249927947979)), 0, by norm_num⟩
  | 3 => ⟨((-14983651221/562949953421312), (4106143475/70368744177664)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((3081093195/4503599627370496), (-86065204473/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((3742124895/72057594037927936), (103606397097/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-13112569091/1152921504606846976), (-14326075273/576460752303423488)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((6217718381/4611686018427387904), (28649820803/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-76907003499/590295810358705651712), (-24657000163/295147905179352825856)), (11/590295810358705651712), by norm_num⟩
  | 9 => ⟨((52789468147/4722366482869645213696), (30870423167/9444732965739290427392)), (17/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-4138829863/4722366482869645213696), (82823075/75557863725914323419136)), (13/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((76471984645/1208925819614629174706176), (-22567580329/1208925819614629174706176)), (5/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-40341846793/9671406556917033397649408), (13005233949/4835703278458516698824704)), (31/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (2397/1280)))⁻¹=value ((204800/1418259), (-60160/1418259)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((204800/1418259), (-60160/1418259))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-14416359275/70368744177664), (-258975195/281474976710656)), (9/562949953421312), by norm_num⟩
  | 1 => ⟨((35991443271/281474976710656), (-49286178837/562949953421312)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((-25926163781/1125899906842624), (73250204189/1125899906842624)), (11/1125899906842624), by norm_num⟩
  | 3 => ⟨((-16531976033/2251799813685248), (-50572993961/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 4 => ⟨((52144938563/9007199254740992), (33597968321/9007199254740992)), (7/4503599627370496), by norm_num⟩
  | 5 => ⟨((-32134198865/18014398509481984), (4427032717/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((40333571909/144115188075855872), (-3008556065/9007199254740992)), (25/144115188075855872), by norm_num⟩
  | 7 => ⟨((955308729/144115188075855872), (114649222939/1152921504606846976)), (59/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-38153937109/2305843009213693952), (-16482237169/1152921504606846976)), (37/2305843009213693952), by norm_num⟩
  | 9 => ⟨((85416912587/18446744073709551616), (-9149085177/18446744073709551616)), (85/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-41546376277/73786976294838206464), (3653864547/4611686018427387904)), (101/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-7436094541/147573952589676412928), (-57275988091/295147905179352825856)), (15/36893488147419103232), by norm_num⟩
  | 12 => ⟨((11086233511/295147905179352825856), (39771103359/2361183241434822606848)), (141/1180591620717411303424), by norm_num⟩
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
  | 0 => ⟨((59/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/94859209), (-3068160/94859209)), 0, by norm_num⟩
  | 1 => ⟨((-68295058227200/8998269532105681), (37073190912000/8998269532105681)), 0, by norm_num⟩
  | 2 => ⟨((14663640029/35184372088832), (-54204957359/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-45745715533/2251799813685248), (70414326641/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((28396796731/36028797018963968), (-83592142645/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-3653840541/288230376151711744), (92531785195/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((-8248103777/4611686018427387904), (-12023094159/1152921504606846976)), (7/9223372036854775808), by norm_num⟩
  | 7 => ⟨((5212326699/18446744073709551616), (93747912789/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-16687600333/590295810358705651712), (-21185855799/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((22487322885/9444732965739290427392), (34542595429/18889465931478580854784)), (3/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-13692288945/75557863725914323419136), (-11781488919/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((61909152053/4835703278458516698824704), (9839899957/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-32817100701/38685626227668133590597632), (5992013263/77371252455336267181195264)), (29/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (2397/1280)))⁻¹=value ((12083200/94859209), (-3068160/94859209)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/94859209), (-3068160/94859209))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-58830563253/2251799813685248), (7328652231/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 1 => ⟨((16905096595/1125899906842624), (-36310269447/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-858166961/562949953421312), (92791186437/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 3 => ⟨((-7796263191/4503599627370496), (-29761101977/9007199254740992)), (15/18014398509481984), by norm_num⟩
  | 4 => ⟨((73626705687/72057594037927936), (33891612733/72057594037927936)), (23/72057594037927936), by norm_num⟩
  | 5 => ⟨((-84150816751/288230376151711744), (21780996737/288230376151711744)), (31/288230376151711744), by norm_num⟩
  | 6 => ⟨((48675320965/1152921504606846976), (-70482618823/1152921504606846976)), (21/576460752303423488), by norm_num⟩
  | 7 => ⟨((2721473337/1152921504606846976), (78532419415/4611686018427387904)), (25/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-6907959227/2305843009213693952), (-21511238601/9223372036854775808)), (31/9223372036854775808), by norm_num⟩
  | 9 => ⟨((118400288541/147573952589676412928), (-8327173759/73786976294838206464)), (145/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-14074162435/147573952589676412928), (20556868815/147573952589676412928)), (43/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-20952852249/2361183241434822606848), (-79108524139/2361183241434822606848)), (51/590295810358705651712), by norm_num⟩
  | 12 => ⟨((7598782947/1180591620717411303424), (27588094195/9444732965739290427392)), (15/590295810358705651712), by norm_num⟩
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
  | 0 => ⟨((67/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/120664009), (-3068160/120664009)), 0, by norm_num⟩
  | 1 => ⟨((-89434350387200/14559803067952081), (42100064256000/14559803067952081)), 0, by norm_num⟩
  | 2 => ⟨((43979865055/140737488355328), (-17064614667/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-4133462697/281474976710656), (9998754409/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((5486816879/9007199254740992), (-21555810673/18014398509481984)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((-22393192495/1152921504606846976), (87369635035/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((1299688649/9223372036854775808), (-5252424033/1152921504606846976)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((460321233/9223372036854775808), (38491076199/147573952589676412928)), (9/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-29060301703/4722366482869645213696), (-67037285203/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5009239771/9444732965739290427392), (13768764427/18889465931478580854784)), (13/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-47660101503/1208925819614629174706176), (-41952176085/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((51892115559/19342813113834066795298816), (28470604675/19342813113834066795298816)), (19/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-13249936413/77371252455336267181195264), (-15345018801/309485009821345068724781056)), (43/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (2397/1280)))⁻¹=value ((13721600/120664009), (-3068160/120664009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/120664009), (-3068160/120664009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-50538914315/18014398509481984), (6325386551/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((25924189473/18014398509481984), (-41991644671/18014398509481984)), (15/36028797018963968), by norm_num⟩
  | 2 => ⟨((2623506917/72057594037927936), (98077594533/72057594037927936)), (11/36028797018963968), by norm_num⟩
  | 3 => ⟨((-43270368941/144115188075855872), (-14723125353/36028797018963968)), (21/144115188075855872), by norm_num⟩
  | 4 => ⟨((86711435101/576460752303423488), (13524608585/288230376151711744)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((-93221434583/2305843009213693952), (35190596019/2305843009213693952)), (43/2305843009213693952), by norm_num⟩
  | 6 => ⟨((24678296469/4611686018427387904), (-86766576103/9223372036854775808)), (59/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1191583483/2305843009213693952), (11434174439/4611686018427387904)), (9/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-4250941767/9223372036854775808), (-47732270561/147573952589676412928)), (11/18446744073709551616), by norm_num⟩
  | 9 => ⟨((17514800941/147573952589676412928), (-6110427149/295147905179352825856)), (13/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-32556765973/2361183241434822606848), (49470954139/2361183241434822606848)), (123/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-12688164809/9444732965739290427392), (-93520103571/18889465931478580854784)), (291/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((71442611467/75557863725914323419136), (32711344217/75557863725914323419136)), (343/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((75/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/49915203), (-1022720/49915203)), 0, by norm_num⟩
  | 1 => ⟨((-4194740633600/830509163510403), (5236326400000/2491527490531209)), 0, by norm_num⟩
  | 2 => ⟨((66853133455/281474976710656), (-44903926687/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-47498778981/4503599627370496), (47805898541/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((31141085385/72057594037927936), (-47014798561/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((-17847769929/1152921504606846976), (87368773631/2305843009213693952)), (7/2305843009213693952), by norm_num⟩
  | 6 => ⟨((14970568691/36893488147419103232), (-9693132241/4611686018427387904)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((425933549/590295810358705651712), (66086702539/590295810358705651712)), (17/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-11181999551/9444732965739290427392), (-108320763513/18889465931478580854784)), (9/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((141042629/1180591620717411303424), (85221362321/302231454903657293676544)), (9/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-43597937303/4835703278458516698824704), (-16003385301/1208925819614629174706176)), (19/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((23134383955/38685626227668133590597632), (5672837763/9671406556917033397649408)), (5/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-22703294529/618970019642690137449562112), (-14828303149/618970019642690137449562112)), (21/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (2397/1280)))⁻¹=value ((5120000/49915203), (-1022720/49915203)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/49915203), (-1022720/49915203))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-74649110479/288230376151711744), (14523116335/72057594037927936)), (17/288230376151711744), by norm_num⟩
  | 1 => ⟨((2000860895/18014398509481984), (-81158756477/288230376151711744)), (1/18014398509481984), by norm_num⟩
  | 2 => ⟨((16608133239/576460752303423488), (44516170039/288230376151711744)), (3/72057594037927936), by norm_num⟩
  | 3 => ⟨((-48688320895/1152921504606846976), (-50026225381/1152921504606846976)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((43813351147/2305843009213693952), (16250826283/4611686018427387904)), (19/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-5585681069/1152921504606846976), (44414302359/18446744073709551616)), (51/18446744073709551616), by norm_num⟩
  | 6 => ⟨((42793654285/73786976294838206464), (-92063895221/73786976294838206464)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((25632144055/295147905179352825856), (11572196797/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-72688599649/1180591620717411303424), (-45961872299/1180591620717411303424)), (107/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((18070548575/1180591620717411303424), (-7530815611/2361183241434822606848)), (1/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-32818211061/18889465931478580854784), (12995949963/4722366482869645213696)), (151/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-26948022797/151115727451828646838272), (-24150177191/37778931862957161709568)), (357/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((36736948065/302231454903657293676544), (33845420849/604462909807314587353088)), (421/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((83/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/182104009), (-3068160/182104009)), 0, by norm_num⟩
  | 1 => ⟨((-139765998387200/33161870093872081), (52153810944000/33161870093872081)), 0, by norm_num⟩
  | 2 => ⟨((6454882489/35184372088832), (-15327259819/140737488355328)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-34429925155/4503599627370496), (59703435495/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((43374227389/144115188075855872), (-53865301395/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-25129599589/2305843009213693952), (46070507267/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 6 => ⟨((12555958527/36893488147419103232), (-75581118525/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-17130205737/2361183241434822606848), (119650783927/2361183241434822606848)), (19/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-3335309769/37778931862957161709568), (-91658832071/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((115977297/4722366482869645213696), (33998597517/302231454903657293676544)), (17/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-5062701503/2417851639229258349412352), (-24388181293/4835703278458516698824704)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((2712103859/19342813113834066795298816), (67388953205/309485009821345068724781056)), (29/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-648244179/77371252455336267181195264), (-22237087267/2475880078570760549798248448)), (13/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (2397/1280)))⁻¹=value ((16998400/182104009), (-3068160/182104009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/182104009), (-3068160/182104009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47914528279/2305843009213693952), (53442618175/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 1 => ⟨((3688344165/576460752303423488), (-67818733871/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((24168123511/4611686018427387904), (70825914887/4611686018427387904)), (23/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-11637608717/2305843009213693952), (-9249704943/2305843009213693952)), (25/9223372036854775808), by norm_num⟩
  | 4 => ⟨((77563330269/36893488147419103232), (5663112733/36893488147419103232)), (5/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-75422789125/147573952589676412928), (46769074781/147573952589676412928)), (27/73786976294838206464), by norm_num⟩
  | 6 => ⟨((8013001249/147573952589676412928), (-85790043259/590295810358705651712)), (37/295147905179352825856), by norm_num⟩
  | 7 => ⟨((28526310695/2361183241434822606848), (41387022049/1180591620717411303424)), (47/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-68590458461/9444732965739290427392), (-19508275463/4722366482869645213696)), (115/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((33033417175/18889465931478580854784), (-16017389705/37778931862957161709568)), (137/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-7323661987/37778931862957161709568), (48459179161/151115727451828646838272)), (81/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-6367996951/302231454903657293676544), (-88572733455/1208925819614629174706176)), (383/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((16792232523/1208925819614629174706176), (31048146213/4835703278458516698824704)), (451/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((91/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/217739209), (-3068160/217739209)), 0, by norm_num⟩
  | 1 => ⟨((-168958354227200/47410363135945681), (57180684288000/47410363135945681)), 0, by norm_num⟩
  | 2 => ⟨((40537198515/281474976710656), (-10797929181/140737488355328)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-50645843027/9007199254740992), (38714372595/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((60629929663/288230376151711744), (-16109208313/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-8562953481/1152921504606846976), (12739264603/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((8854625671/36893488147419103232), (-77506779341/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-15515234125/2361183241434822606848), (14266130437/590295810358705651712)), (7/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((8382228103/75557863725914323419136), (-81646538885/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((6928415803/2417851639229258349412352), (14212858033/302231454903657293676544)), (5/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-1097602223/2417851639229258349412352), (-9634461621/4835703278458516698824704)), (17/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((20713706107/618970019642690137449562112), (25398500771/309485009821345068724781056)), (15/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-4977427159/2475880078570760549798248448), (-8111911473/2475880078570760549798248448)), (25/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (2397/1280)))⁻¹=value ((18636800/217739209), (-3068160/217739209)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/217739209), (-3068160/217739209))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-26784444771/18446744073709551616), (20997758387/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 1 => ⟨((6615066897/36893488147419103232), (-100174330117/36893488147419103232)), (7/9223372036854775808), by norm_num⟩
  | 2 => ⟨((12477788011/18446744073709551616), (12526621291/9223372036854775808)), (21/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-77775448703/147573952589676412928), (-48048123655/147573952589676412928)), (45/147573952589676412928), by norm_num⟩
  | 4 => ⟨((61083007285/295147905179352825856), (-462295601/73786976294838206464)), (73/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-56777058745/1180591620717411303424), (42564824349/1180591620717411303424)), (51/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((20796106661/4722366482869645213696), (-71243424517/4722366482869645213696)), (35/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((13655905115/9444732965739290427392), (66244709423/18889465931478580854784)), (89/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-28953521279/37778931862957161709568), (-1847152973/4722366482869645213696)), (55/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((54178589403/302231454903657293676544), (-14987964533/302231454903657293676544)), (131/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5862154989/302231454903657293676544), (40576753149/1208925819614629174706176)), (309/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-21685245507/9671406556917033397649408), (-72991636897/9671406556917033397649408)), (365/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((55262366555/38685626227668133590597632), (25571958451/38685626227668133590597632)), (215/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((99/8), (2397/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/28516801), (-1022720/85550403)), 0, by norm_num⟩
  | 1 => ⟨((-22315007180800/7318871453462409), (2303983616000/2439623817820803)), 0, by norm_num⟩
  | 2 => ⟨((8077475143/70368744177664), (-7814868183/140737488355328)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-9462416585/2251799813685248), (25935773421/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((21440287153/144115188075855872), (-40022056583/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-46545233117/9223372036854775808), (29394590991/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 6 => ⟨((47587653103/295147905179352825856), (-83211493149/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-22116958253/4722366482869645213696), (57140153963/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((17026102827/151115727451828646838272), (-38227333385/75557863725914323419136)), (11/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-862123269/604462909807314587353088), (49947084951/2417851639229258349412352)), (17/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-2597354181/38685626227668133590597632), (-63791956051/77371252455336267181195264)), (13/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((18767738833/2475880078570760549798248448), (79638446335/2475880078570760549798248448)), (5/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-19477427169/39614081257132168796771975168), (-48536003633/39614081257132168796771975168)), (15/39614081257132168796771975168), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (2397/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (2397/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (2397/1280)))⁻¹=value ((2252800/28516801), (-1022720/85550403)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/28516801), (-1022720/85550403))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-12911250611/147573952589676412928), (58204843369/295147905179352825856)), (21/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-4727603853/295147905179352825856), (-66395465513/295147905179352825856)), (23/295147905179352825856), by norm_num⟩
  | 2 => ⟨((42294712747/590295810358705651712), (63749153129/590295810358705651712)), (33/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-28925995105/590295810358705651712), (-858073867/36893488147419103232)), (37/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((86651297557/4722366482869645213696), (-11065719993/4722366482869645213696)), (61/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-38524989877/9444732965739290427392), (34240676999/9444732965739290427392)), (43/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((11597700947/37778931862957161709568), (-53345232913/37778931862957161709568)), (59/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((11519654027/75557863725914323419136), (1498746053/4722366482869645213696)), (19/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-88420292105/1208925819614629174706176), (-20166862353/604462909807314587353088)), (187/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((40274345749/2417851639229258349412352), (-12524444189/2417851639229258349412352)), (7/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-4250635285/2417851639229258349412352), (15414255697/4835703278458516698824704)), (265/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-16787020927/77371252455336267181195264), (-27305487721/38685626227668133590597632)), (313/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((10332257961/77371252455336267181195264), (19103236259/309485009821345068724781056)), (23/19342813113834066795298816), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((56521590127/274877906944), (15342479717/137438953472)), (157/68719476736), by norm_num⟩
  | 1 => ⟨((1537052691/137438953472), (85724088785/549755813888)), (699/137438953472), by norm_num⟩
  | 2 => ⟨((-66452022597/2199023255552), (3146579403/137438953472)), (13869/2199023255552), by norm_num⟩
  | 3 => ⟨((-16084218347/8796093022208), (5474835129/8796093022208)), (6009/1099511627776), by norm_num⟩
  | 4 => ⟨((-43086508325/70368744177664), (89798496955/70368744177664)), (126863/35184372088832), by norm_num⟩
  | 5 => ⟨((-21455819085/70368744177664), (-7431017957/140737488355328)), (271691/140737488355328), by norm_num⟩
  | 6 => ⟨((54293833705/2251799813685248), (-18185498037/1125899906842624)), (247255/281474976710656), by norm_num⟩
  | 7 => ⟨((-40164323397/9007199254740992), (21244794315/2251799813685248)), (3159505/9007199254740992), by norm_num⟩
  | 8 => ⟨((-26601909895/18014398509481984), (-62154997519/36028797018963968)), (4531757/36028797018963968), by norm_num⟩
  | 9 => ⟨((124973121831/288230376151711744), (437892861/144115188075855872)), (11879853/288230376151711744), by norm_num⟩
  | 10 => ⟨((-17883028687/288230376151711744), (43206415847/576460752303423488)), (1803025/144115188075855872), by norm_num⟩
  | 11 => ⟨((-24243522315/4611686018427387904), (-92314051451/4611686018427387904)), (16406593/4611686018427387904), by norm_num⟩
  | 12 => ⟨((37268468101/9223372036854775808), (1913715207/1152921504606846976)), (4414945/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((56521590127/274877906944), (15342479717/137438953472)), (629/274877906944), by norm_num⟩
  | 1 => ⟨((1537052691/137438953472), (85724088785/549755813888)), (2797/549755813888), by norm_num⟩
  | 2 => ⟨((-66452022597/2199023255552), (3146579403/137438953472)), (6935/1099511627776), by norm_num⟩
  | 3 => ⟨((-16084218347/8796093022208), (5474835129/8796093022208)), (96145/17592186044416), by norm_num⟩
  | 4 => ⟨((-43086508325/70368744177664), (89798496955/70368744177664)), (253729/70368744177664), by norm_num⟩
  | 5 => ⟨((-21455819085/70368744177664), (-7431017957/140737488355328)), (271697/140737488355328), by norm_num⟩
  | 6 => ⟨((54293833705/2251799813685248), (-18185498037/1125899906842624)), (1978131/2251799813685248), by norm_num⟩
  | 7 => ⟨((-40164323397/9007199254740992), (21244794315/2251799813685248)), (1579933/4503599627370496), by norm_num⟩
  | 8 => ⟨((-26601909895/18014398509481984), (-62154997519/36028797018963968)), (4533199/36028797018963968), by norm_num⟩
  | 9 => ⟨((124973121831/288230376151711744), (437892861/144115188075855872)), (11891383/288230376151711744), by norm_num⟩
  | 10 => ⟨((-17883028687/288230376151711744), (43206415847/576460752303423488)), (7235159/576460752303423488), by norm_num⟩
  | 11 => ⟨((-24243522315/4611686018427387904), (-92314051451/4611686018427387904)), (16591061/4611686018427387904), by norm_num⟩
  | 12 => ⟨((37268468101/9223372036854775808), (1913715207/1152921504606846976)), (9198825/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile008Gamma
