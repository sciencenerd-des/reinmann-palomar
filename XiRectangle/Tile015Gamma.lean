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
namespace Reinmann.XiRectangle.Tile015Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4371/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4371/640))
  have he : value ((3/4), (4371/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/312200041), (-5594880/312200041)), 0, by norm_num⟩
  | 1 => ⟨((-224451591372800/97468865600401681), (122603962368000/97468865600401681)), 0, by norm_num⟩
  | 2 => ⟨((39151365551/562949953421312), (-4558476975/70368744177664)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-33512580397/18014398509481984), (52181329235/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((11337167159/288230376151711744), (-68211631895/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-5905977313/18446744073709551616), (83106848601/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-17196749601/590295810358705651712), (-95026943157/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 7 => ⟨((23280125983/9444732965739290427392), (12723692571/2361183241434822606848)), (7/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-20369030025/151115727451828646838272), (-50482408583/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((60226030315/9671406556917033397649408), (45013536757/9671406556917033397649408)), (17/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-40271986369/154742504910672534362390528), (-33283850931/309485009821345068724781056)), (25/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((99998836471/9903520314283042199192993792), (14284950517/9903520314283042199192993792)), (9/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-58200045831/158456325028528675187087900672), (3157549855/79228162514264337593543950336)), (13/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (4371/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (4371/1280)))⁻¹=value ((21913600/312200041), (-5594880/312200041)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/312200041), (-5594880/312200041))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((90193007263/34359738368), (8589079765/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((10956800/312200041), (-2797440/312200041)), 0, by norm_num⟩
  | 2 => ⟨((-56112897843200/97468865600401681), (30650990592000/97468865600401681)), 0, by norm_num⟩
  | 3 => ⟨((52201820735/4503599627370496), (-1519492325/140737488355328)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-33512580397/144115188075855872), (52181329235/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((9069733727/2305843009213693952), (-13642326379/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-7874636417/295147905179352825856), (27702282867/73786976294838206464)), (9/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-19653428115/9444732965739290427392), (-108602220751/9444732965739290427392)), (11/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((23280125983/151115727451828646838272), (12723692571/37778931862957161709568)), (7/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-36211608933/4835703278458516698824704), (-22436626037/2417851639229258349412352)), (11/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((12045206063/38685626227668133590597632), (18005414703/77371252455336267181195264)), (7/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-58577434719/4951760157141521099596496896), (-24206437041/4951760157141521099596496896)), (19/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((66665890981/158456325028528675187087900672), (9523300345/158456325028528675187087900672)), (25/158456325028528675187087900672), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (93/20480)), 0, by norm_num⟩
  | 45 => ⟨((103616839193/4080638361600), (-184791/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-48999753836239/1915179604377600), (3808183864583/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((28677518847/1099511627776), (-14325869775/2199023255552)), (1/2199023255552), by norm_num⟩
  | 42 => ⟨((-58709969503/2199023255552), (113996045/17179869184)), (1/2199023255552), by norm_num⟩
  | 41 => ⟨((60152588467/2199023255552), (-14924252721/2199023255552)), (1/2199023255552), by norm_num⟩
  | 40 => ⟨((-61659115989/2199023255552), (15286740885/2199023255552)), (1/1099511627776), by norm_num⟩
  | 39 => ⟨((63238545925/2199023255552), (-3916936589/549755813888)), (1/1099511627776), by norm_num⟩
  | 38 => ⟨((-32450087687/1099511627776), (8033674609/1099511627776)), (1/1099511627776), by norm_num⟩
  | 37 => ⟨((33325764021/1099511627776), (-2060943359/274877906944)), (1/1099511627776), by norm_num⟩
  | 36 => ⟨((-34250047933/1099511627776), (16930272781/2199023255552)), (1/1099511627776), by norm_num⟩
  | 35 => ⟨((70454143089/2199023255552), (-17397443143/2199023255552)), (1/1099511627776), by norm_num⟩
  | 34 => ⟨((-9065367569/274877906944), (2236392019/274877906944)), (1/1099511627776), by norm_num⟩
  | 33 => ⟨((37358449315/1099511627776), (-18413671417/2199023255552)), (1/2199023255552), by norm_num⟩
  | 32 => ⟨((-77047729745/2199023255552), (18967651361/2199023255552)), (1/2199023255552), by norm_num⟩
  | 31 => ⟨((79528654355/2199023255552), (-4889000675/549755813888)), (1/2199023255552), by norm_num⟩
  | 30 => ⟨((-41087325845/1099511627776), (10091013605/1099511627776)), (1/1099511627776), by norm_num⟩
  | 29 => ⟨((85002762573/2199023255552), (-5212365893/549755813888)), (1/1099511627776), by norm_num⟩
  | 28 => ⟨((-88032456803/2199023255552), (21562562149/2199023255552)), (1/1099511627776), by norm_num⟩
  | 27 => ⟨((91286081919/2199023255552), (-22326175659/2199023255552)), (1/1099511627776), by norm_num⟩
  | 26 => ⟨((-5924338453/137438953472), (11572934919/1099511627776)), (1/2199023255552), by norm_num⟩
  | 25 => ⟨((49286174051/1099511627776), (-24028059409/2199023255552)), (1/1099511627776), by norm_num⟩
  | 24 => ⟨((-102669740561/2199023255552), (3122522053/274877906944)), (1/1099511627776), by norm_num⟩
  | 23 => ⟨((107122498615/2199023255552), (-26010880311/2199023255552)), (1/1099511627776), by norm_num⟩
  | 22 => ⟨((-13997368025/274877906944), (3391290279/274877906944)), (1/1099511627776), by norm_num⟩
  | 21 => ⟨((14662071931/274877906944), (-14175240425/1099511627776)), (1/1099511627776), by norm_num⟩
  | 20 => ⟨((-61572176645/1099511627776), (3710699139/274877906944)), (1/1099511627776), by norm_num⟩
  | 19 => ⟨((64802853831/1099511627776), (-1947044559/137438953472)), (1/1099511627776), by norm_num⟩
  | 18 => ⟨((-4274454441/68719476736), (8193111129/549755813888)), (1/1099511627776), by norm_num⟩
  | 17 => ⟨((72400323191/1099511627776), (-8642479311/549755813888)), (1/1099511627776), by norm_num⟩
  | 16 => ⟨((-38454282601/549755813888), (18288050471/1099511627776)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((82015409485/1099511627776), (-19414804105/1099511627776)), (1/549755813888), by norm_num⟩
  | 14 => ⟨((-43924270153/549755813888), (20689604329/1099511627776)), (1/549755813888), by norm_num⟩
  | 13 => ⟨((11821841661/137438953472), (-691990723/34359738368)), (1/1099511627776), by norm_num⟩
  | 12 => ⟨((-51208027885/549755813888), (23817822351/1099511627776)), (1/549755813888), by norm_num⟩
  | 11 => ⟨((27918713203/274877906944), (-12883019113/549755813888)), (1/549755813888), by norm_num⟩
  | 10 => ⟨((-61386815577/549755813888), (7015437867/274877906944)), (1/274877906944), by norm_num⟩
  | 9 => ⟨((17040168933/137438953472), (-15403589519/549755813888)), (1/274877906944), by norm_num⟩
  | 8 => ⟨((-38307267193/274877906944), (1067158125/34359738368)), (1/274877906944), by norm_num⟩
  | 7 => ⟨((87461938635/549755813888), (-4788239143/137438953472)), (1/274877906944), by norm_num⟩
  | 6 => ⟨((-101887421161/549755813888), (21809085345/549755813888)), (1/274877906944), by norm_num⟩
  | 5 => ⟨((61006202069/274877906944), (-6330913631/137438953472)), (1/274877906944), by norm_num⟩
  | 4 => ⟨((-76025921657/274877906944), (7548873263/137438953472)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((50438346959/137438953472), (-4675753563/68719476736)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((-74998647055/137438953472), (12299173755/137438953472)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((18389804277/17179869184), (-4506156129/34359738368)), (1/68719476736), by norm_num⟩
  | 0 => ⟨((-5072415835/34359738368), (34356319059/137438953472)), (3/274877906944), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (4371/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (4371/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (4371/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((90193007263/34359738368), (8589079765/34359738368)), (1/34359738368), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (4371/1280))) (z:=((-21/128), (4371/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((90193007263/34359738368), (8589079765/34359738368))) (r:=(1/34359738368)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((70744037697/2147483648), (1635075895/134217728)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((123346875253/68719476736), (2224239267/17179869184)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((883234801228800/97468865600401681), (-233665715969760/97468865600401681)), 0, by norm_num⟩
  | 3 => ⟨((-57277731055/562949953421312), (32544088015/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((28195446643/18014398509481984), (-27573210277/18014398509481984)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-14538748875/576460752303423488), (3035389161/72057594037927936)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((6292571539/18446744073709551616), (-86610215453/73786976294838206464)), (35/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-2043113721/2361183241434822606848), (76894781289/2361183241434822606848)), (41/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-7823372775/37778931862957161709568), (-67024802945/75557863725914323419136)), (51/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((29746347551/2417851639229258349412352), (7057263603/302231454903657293676544)), (147/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-20507246603/38685626227668133590597632), (-44901309007/77371252455336267181195264)), (203/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((12421239533/618970019642690137449562112), (2015081461/154742504910672534362390528)), (267/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-55718095893/79228162514264337593543950336), (-4629612445/19807040628566084398385987584)), (89/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((42021443905/2147483648), (37655786413/4294967296)), (5/4294967296), by norm_num⟩
  | 1 => ⟨((88987136885/68719476736), (2224239267/17179869184)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((883234801228800/97468865600401681), (-233665715969760/97468865600401681)), 0, by norm_num⟩
  | 3 => ⟨((-57277731055/562949953421312), (32544088015/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((28195446643/18014398509481984), (-27573210277/18014398509481984)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-14538748875/576460752303423488), (3035389161/72057594037927936)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((6292571539/18446744073709551616), (-86610215453/73786976294838206464)), (35/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-2043113721/2361183241434822606848), (76894781289/2361183241434822606848)), (41/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-7823372775/37778931862957161709568), (-67024802945/75557863725914323419136)), (51/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((29746347551/2417851639229258349412352), (7057263603/302231454903657293676544)), (147/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-20507246603/38685626227668133590597632), (-44901309007/77371252455336267181195264)), (203/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((12421239533/618970019642690137449562112), (2015081461/154742504910672534362390528)), (267/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-55718095893/79228162514264337593543950336), (-4629612445/19807040628566084398385987584)), (89/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((87989698757/4294967296), (37655786413/4294967296)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((88987136885/68719476736), (2224239267/17179869184)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((883234801228800/97468865600401681), (-233665715969760/97468865600401681)), 0, by norm_num⟩
  | 3 => ⟨((-57277731055/562949953421312), (32544088015/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((28195446643/18014398509481984), (-27573210277/18014398509481984)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-14538748875/576460752303423488), (3035389161/72057594037927936)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((6292571539/18446744073709551616), (-86610215453/73786976294838206464)), (35/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-2043113721/2361183241434822606848), (76894781289/2361183241434822606848)), (41/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-7823372775/37778931862957161709568), (-67024802945/75557863725914323419136)), (51/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((29746347551/2417851639229258349412352), (7057263603/302231454903657293676544)), (147/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-20507246603/38685626227668133590597632), (-44901309007/77371252455336267181195264)), (203/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((12421239533/618970019642690137449562112), (2015081461/154742504910672534362390528)), (267/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-55718095893/79228162514264337593543950336), (-4629612445/19807040628566084398385987584)), (89/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((448903182745600/97468865600401681), (-245207924736000/97468865600401681)), 0, by norm_num⟩
  | 1 => ⟨((-39151365551/140737488355328), (4558476975/17592186044416)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((12567217649/1125899906842624), (-19567998463/1125899906842624)), (3/4503599627370496), by norm_num⟩
  | 3 => ⟨((-11337167159/36028797018963968), (68211631895/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((7382471641/2305843009213693952), (-51941780375/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 5 => ⟨((12897562201/36893488147419103232), (71270207367/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-40740220469/1180591620717411303424), (-22266461999/295147905179352825856)), (11/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((40738060049/18889465931478580854784), (25241204291/9444732965739290427392)), (9/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-67754284103/604462909807314587353088), (-50640228851/604462909807314587353088)), (7/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((3146248935/604462909807314587353088), (1300150427/604462909807314587353088)), (3/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-68749200073/309485009821345068724781056), (-9820903481/309485009821345068724781056)), (9/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((43650034373/4951760157141521099596496896), (-2368162391/2475880078570760549798248448)), (29/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-3227202469/9903520314283042199192993792), (19321313729/158456325028528675187087900672)), (11/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39151365551/140737488355328), (-4558476975/17592186044416)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-12567217649/562949953421312), (19567998463/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 2 => ⟨((34011501477/36028797018963968), (-51158723921/18014398509481984)), (5/36028797018963968), by norm_num⟩
  | 3 => ⟨((-7382471641/576460752303423488), (51941780375/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((-16121952751/9223372036854775808), (-11135969901/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((3819395669/18446744073709551616), (16699846499/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-35645802543/2361183241434822606848), (-44172107509/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 7 => ⟨((33877142051/37778931862957161709568), (25320114425/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-28316240415/604462909807314587353088), (-11701353843/604462909807314587353088)), (3/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((42968250045/19342813113834066795298816), (12276129351/38685626227668133590597632)), (19/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-120037594525/1237940039285380274899124224), (6512446575/618970019642690137449562112)), (1/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((9681607407/2475880078570760549798248448), (-28981970593/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-11473244599/79228162514264337593543950336), (998167623/9903520314283042199192993792)), (11/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((33512580397/2251799813685248), (-52181329235/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-11337167159/9007199254740992), (34105815947/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((7382471641/288230376151711744), (-51941780375/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 3 => ⟨((2686992125/576460752303423488), (3711989967/144115188075855872)), (5/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-25462637793/36893488147419103232), (-55666154997/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 5 => ⟨((17822901271/295147905179352825856), (44172107509/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-39523332393/9444732965739290427392), (-3692516687/1180591620717411303424)), (1/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((75509974439/302231454903657293676544), (31203610247/302231454903657293676544)), (15/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-64452375067/4835703278458516698824704), (-9207097013/4835703278458516698824704)), (15/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((50015664385/77371252455336267181195264), (-10854077625/154742504910672534362390528)), (13/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-70998454317/2475880078570760549798248448), (26566806377/2475880078570760549798248448)), (23/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((11473244599/9903520314283042199192993792), (-998167623/1237940039285380274899124224)), (19/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-52977076523/1267650600228229401496703205376), (61288651767/1267650600228229401496703205376)), (1/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11337167159/18014398509481984), (-68211631895/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3691235821/144115188075855872), (51941780375/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((-16121952751/2305843009213693952), (-11135969901/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 3 => ⟨((25462637793/18446744073709551616), (55666154997/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-22278626589/147573952589676412928), (-27607567193/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 5 => ⟨((59284998589/4722366482869645213696), (11077550061/1180591620717411303424)), (13/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-33035613817/37778931862957161709568), (-27303158967/75557863725914323419136)), (7/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((64452375067/1208925819614629174706176), (9207097013/1208925819614629174706176)), (15/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-112535244865/38685626227668133590597632), (763177333/2417851639229258349412352)), (15/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((11093508487/77371252455336267181195264), (-33208507971/618970019642690137449562112)), (7/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((-31551422647/4951760157141521099596496896), (10979843853/2475880078570760549798248448)), (13/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((1241650231/4951760157141521099596496896), (-45966488825/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-20961324911/2535301200456458802993406410752), (84020764635/5070602400912917605986812821504)), (41/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5905977313/576460752303423488), (-83106848601/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 1 => ⟨((1612195275/288230376151711744), (71270207367/2305843009213693952)), (7/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-3819395669/2305843009213693952), (-16699846499/4611686018427387904)), (9/18446744073709551616), by norm_num⟩
  | 3 => ⟨((17822901271/73786976294838206464), (44172107509/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-59284998589/2361183241434822606848), (-11077550061/590295810358705651712)), (13/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((79285473161/37778931862957161709568), (4095473845/4722366482869645213696)), (9/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-45116662547/302231454903657293676544), (-12889935819/604462909807314587353088)), (11/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((22507048973/2417851639229258349412352), (-9768669863/9671406556917033397649408)), (25/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-39936630553/77371252455336267181195264), (29887657173/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((31551422647/1237940039285380274899124224), (-10979843853/618970019642690137449562112)), (27/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-43706088131/39614081257132168796771975168), (50563137707/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((25153589893/633825300114114700748351602688), (-50412458781/633825300114114700748351602688)), (13/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-4885349403/5070602400912917605986812821504), (2825731819/633825300114114700748351602688)), (23/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-17196749601/9223372036854775808), (-95026943157/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 1 => ⟨((40740220469/36893488147419103232), (22266461999/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-17822901271/73786976294838206464), (-44172107509/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 3 => ⟨((4940416549/147573952589676412928), (3692516687/147573952589676412928)), (9/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-33035613817/9444732965739290427392), (-27303158967/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((45116662547/151115727451828646838272), (12889935819/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-13129111901/604462909807314587353088), (5698390753/2417851639229258349412352)), (31/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((26624420369/19342813113834066795298816), (-9962552391/19342813113834066795298816)), (5/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-23663566985/309485009821345068724781056), (16469765779/309485009821345068724781056)), (11/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((36421740109/9903520314283042199192993792), (-42135948089/9903520314283042199192993792)), (23/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-11528728701/79228162514264337593543950336), (46211420549/158456325028528675187087900672)), (25/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((4885349403/1267650600228229401496703205376), (-2825731819/158456325028528675187087900672)), (49/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((1493000509/40564819207303340847894502572032), (80365180679/81129638414606681695789005144064)), (47/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23280125983/73786976294838206464), (-12723692571/18446744073709551616)), (7/73786976294838206464), by norm_num⟩
  | 1 => ⟨((40738060049/295147905179352825856), (50482408583/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-67754284101/2361183241434822606848), (-25320114425/1180591620717411303424)), (17/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((37754987219/9444732965739290427392), (3900451281/2361183241434822606848)), (19/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((-64452375067/151115727451828646838272), (-4603548507/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((22507048973/604462909807314587353088), (-4884334931/1208925819614629174706176)), (7/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-26624420369/9671406556917033397649408), (9962552391/9671406556917033397649408)), (21/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((54088153109/309485009821345068724781056), (-9411294731/77371252455336267181195264)), (7/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-46827951569/4951760157141521099596496896), (211620275/19342813113834066795298816)), (33/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((8234806215/19807040628566084398385987584), (-66016315069/79228162514264337593543950336)), (19/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-15353955267/1267650600228229401496703205376), (71046971449/1267650600228229401496703205376)), (21/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-639857361/5070602400912917605986812821504), (-34442220291/10141204801825835211973625643008)), (43/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((4478028105/81129638414606681695789005144064), (15165779107/81129638414606681695789005144064)), (11/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-20369030025/590295810358705651712), (-50482408583/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((67754284103/4722366482869645213696), (12660057213/1180591620717411303424)), (9/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((-56632480829/18889465931478580854784), (-11701353843/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((32226187533/75557863725914323419136), (4603548507/75557863725914323419136)), (19/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-112535244865/2417851639229258349412352), (12210837327/2417851639229258349412352)), (19/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((39936630553/9671406556917033397649408), (-29887657173/19342813113834066795298816)), (33/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-47327133971/154742504910672534362390528), (16469765779/77371252455336267181195264)), (13/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((46827951569/2475880078570760549798248448), (-211620275/9671406556917033397649408)), (9/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-144752453/154742504910672534362390528), (74268354453/39614081257132168796771975168)), (47/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((19192444083/633825300114114700748351602688), (-44404357155/316912650057057350374175801344)), (57/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((3519215485/10141204801825835211973625643008), (11839513225/1267650600228229401496703205376)), (65/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((-26868168629/162259276829213363391578010288128), (-45497337321/81129638414606681695789005144064)), (71/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((46887996633/2596148429267413814265248164610048), (19684993389/649037107316853453566312041152512)), (75/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-60226030315/18889465931478580854784), (-45013536757/18889465931478580854784)), (17/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((3146248935/2361183241434822606848), (20802406833/37778931862957161709568)), (15/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-85936500089/302231454903657293676544), (-1534516169/37778931862957161709568)), (7/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((195373689/4722366482869645213696), (-1356759703/302231454903657293676544)), (37/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((-11093508487/2417851639229258349412352), (33208507969/19342813113834066795298816)), (39/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((31551422647/77371252455336267181195264), (-43919375411/154742504910672534362390528)), (9/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-36421740109/1237940039285380274899124224), (5266993511/154742504910672534362390528)), (31/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((32939224861/19807040628566084398385987584), (-66016315069/19807040628566084398385987584)), (45/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((-4798111021/79228162514264337593543950336), (88808714311/316912650057057350374175801344)), (31/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((-977559857/1267650600228229401496703205376), (-105240117555/5070602400912917605986812821504)), (5/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((513107387/1267650600228229401496703205376), (55607856725/40564819207303340847894502572032)), (49/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((-15629332211/324518553658426726783156020576256), (-6561664463/81129638414606681695789005144064)), (7/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((10971788591/2596148429267413814265248164610048), (10935301777/2596148429267413814265248164610048)), (61/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-40271986369/151115727451828646838272), (-33283850931/302231454903657293676544)), (25/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((68749200073/604462909807314587353088), (4910451741/302231454903657293676544)), (3/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((-120037594523/4835703278458516698824704), (13024893149/4835703278458516698824704)), (3/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((17749613579/4835703278458516698824704), (-26566806375/19342813113834066795298816)), (35/19342813113834066795298816), by norm_num⟩
  | 4 => ⟨((-31551422647/77371252455336267181195264), (21959687705/77371252455336267181195264)), (39/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((43706088131/1237940039285380274899124224), (-25281568853/618970019642690137449562112)), (19/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((-23057457403/9903520314283042199192993792), (11552855137/2475880078570760549798248448)), (35/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((15353955267/158456325028528675187087900672), (-8880871431/19807040628566084398385987584)), (27/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((879803871/633825300114114700748351602688), (11839513225/316912650057057350374175801344)), (39/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((-513107387/633825300114114700748351602688), (-55607856725/20282409603651670423947251286016)), (27/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((34384530863/324518553658426726783156020576256), (28871323637/162259276829213363391578010288128)), (17/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((-13166146309/1298074214633706907132624082305024), (-52489448529/5192296858534827628530496329220096)), (41/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((8501584955/10384593717069655257060992658440192), (10048459273/20769187434139310514121985316880384)), (47/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/936600123), (-466240/312200041)), 0, by norm_num⟩
  | 1 => ⟨((-56112897843200/292406596801205043), (10216996864000/97468865600401681)), 0, by norm_num⟩
  | 2 => ⟨((52201820735/9007199254740992), (-1519492325/281474976710656)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-44683440529/288230376151711744), (69575105647/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((30232445757/9223372036854775808), (-90948842527/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-7874636417/295147905179352825856), (27702282867/73786976294838206464)), (9/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-5732249867/2361183241434822606848), (-31675647719/2361183241434822606848)), (3/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((31040167977/151115727451828646838272), (4241230857/9444732965739290427392)), (5/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-6789676675/604462909807314587353088), (-67309878111/4835703278458516698824704)), (15/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((40150686877/77371252455336267181195264), (30009024505/77371252455336267181195264)), (3/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-53695981825/2475880078570760549798248448), (-11094616977/1237940039285380274899124224)), (17/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((66665890981/79228162514264337593543950336), (9523300345/79228162514264337593543950336)), (25/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-19400015277/633825300114114700748351602688), (8420132947/2535301200456458802993406410752)), (35/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((88014821057/4294967296), (37649372303/4294967296)), (7/4294967296), by norm_num⟩
  | 1 => ⟨((88973949601/68719476736), (4452080231/34359738368)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((79758641133/8796093022208), (-21134683223/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-7170625425/70368744177664), (32679976893/562949953421312)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((56508988777/36028797018963968), (-27750844735/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-29108258049/1152921504606846976), (24499537373/576460752303423488)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((6247788337/18446744073709551616), (-21900019861/18446744073709551616)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-194763887/295147905179352825856), (77955089003/2361183241434822606848)), (83/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-8247727567/37778931862957161709568), (-34038259895/37778931862957161709568)), (13/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((7750264129/604462909807314587353088), (7174486355/302231454903657293676544)), (37/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-21346246319/38685626227668133590597632), (-5699340321/9671406556917033397649408)), (51/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((51768267225/2475880078570760549798248448), (2033681657/154742504910672534362390528)), (269/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-58143097803/79228162514264337593543950336), (-18255320625/79228162514264337593543950336)), (179/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55681942117/72057594037927936), (51865338027/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 1 => ⟨((4468344053/72057594037927936), (-55660084517/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 2 => ⟨((-12092978303/4611686018427387904), (72759074021/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((5249757611/147573952589676412928), (-73872754311/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 4 => ⟨((5732249867/1180591620717411303424), (63351295437/2361183241434822606848)), (3/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-1358007349/2361183241434822606848), (-47501785597/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((25348126253/604462909807314587353088), (31411276451/604462909807314587353088)), (13/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-24090412125/9671406556917033397649408), (-9002707351/4835703278458516698824704)), (11/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((629249787/4835703278458516698824704), (33283850931/618970019642690137449562112)), (9/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-954850001/154742504910672534362390528), (-8729691983/9903520314283042199192993792)), (7/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((42680033609/158456325028528675187087900672), (-144721035/4951760157141521099596496896)), (23/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-13769397201/1267650600228229401496703205376), (20609401311/5070602400912917605986812821504)), (5/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((65270013719/162259276829213363391578010288128), (-22713858799/81129638414606681695789005144064)), (1/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44007408869/2147483648), (18824687697/2147483648)), (1/536870912), by norm_num⟩
  | 1 => ⟨((44486976931/34359738368), (8904153827/68719476736)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((79758618067/8796093022208), (-21134613835/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-28682491687/281474976710656), (32679695091/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((56509163711/36028797018963968), (-27750361403/18014398509481984)), (19/36028797018963968), by norm_num⟩
  | 5 => ⟨((-29108921139/1152921504606846976), (48997625107/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 6 => ⟨((12497123801/36893488147419103232), (-21899061265/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-48874767/73786976294838206464), (38975346575/1180591620717411303424)), (21/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-8242811553/37778931862957161709568), (-17018114205/18889465931478580854784)), (105/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((30986136985/2417851639229258349412352), (3587109973/151115727451828646838272)), (149/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-21335826389/38685626227668133590597632), (-22798491917/38685626227668133590597632)), (205/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((51741373871/2475880078570760549798248448), (1017155303/77371252455336267181195264)), (135/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-58111227679/79228162514264337593543950336), (-1142343883/4951760157141521099596496896)), (359/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((18427395509/36893488147419103232), (-55435484969/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-5999722985/295147905179352825856), (84426004927/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-6551142705/1180591620717411303424), (-72401480499/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 3 => ⟨((41386890635/37778931862957161709568), (45239795807/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-9052902233/75557863725914323419136), (-5609156509/37778931862957161709568)), (9/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((24090412125/2417851639229258349412352), (36010829405/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-53695981823/77371252455336267181195264), (-11094616977/38685626227668133590597632)), (3/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((104760685823/2475880078570760549798248448), (935324141/154742504910672534362390528)), (25/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((-45728607437/19807040628566084398385987584), (4961864057/19807040628566084398385987584)), (25/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((72125413909/633825300114114700748351602688), (-6747125429/158456325028528675187087900672)), (23/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-51283582207/10141204801825835211973625643008), (8923301671/2535301200456458802993406410752)), (11/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((8072697375/40564819207303340847894502572032), (-37356892505/162259276829213363391578010288128)), (21/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-17035235483/2596148429267413814265248164610048), (68283542053/5192296858534827628530496329220096)), (35/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22003704435/1073741824), (9412343847/1073741824)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((88973953861/68719476736), (8904153847/68719476736)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((39879309009/4398046511104), (-21134614105/8796093022208)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-57364982757/562949953421312), (32679696439/562949953421312)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((28254579697/18014398509481984), (-55500728155/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-7277227413/288230376151711744), (48997633693/1152921504606846976)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((12497098197/36893488147419103232), (-87596266221/73786976294838206464)), (73/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-390973159/590295810358705651712), (38975353711/1180591620717411303424)), (85/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-16485797547/75557863725914323419136), (-17018109473/18889465931478580854784)), (53/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((15493206061/1208925819614629174706176), (57393656615/2417851639229258349412352)), (75/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-42672044041/77371252455336267181195264), (-11399177879/19342813113834066795298816)), (103/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((51741866589/2475880078570760549798248448), (32548399675/2475880078570760549798248448)), (271/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-58111747553/79228162514264337593543950336), (-4569115051/19807040628566084398385987584)), (45/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1310228541/1180591620717411303424), (115842368801/18889465931478580854784)), (3/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-24832134381/37778931862957161709568), (-54287754969/37778931862957161709568)), (1/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((21726965359/151115727451828646838272), (53847902487/302231454903657293676544)), (3/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-48180824249/2417851639229258349412352), (-36010829405/2417851639229258349412352)), (3/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((80543972735/38685626227668133590597632), (33283850931/38685626227668133590597632)), (5/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-109998720115/618970019642690137449562112), (-7856722785/309485009821345068724781056)), (29/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((16005012603/1237940039285380274899124224), (-434163105/309485009821345068724781056)), (5/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-64912872519/79228162514264337593543950336), (3036206443/9903520314283042199192993792)), (25/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((28847014991/633825300114114700748351602688), (-20077428759/633825300114114700748351602688)), (7/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((-44399835561/20282409603651670423947251286016), (25682863597/10141204801825835211973625643008)), (29/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((28108138547/324518553658426726783156020576256), (-56333922193/324518553658426726783156020576256)), (31/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-2977736779/1298074214633706907132624082305024), (110230452673/10384593717069655257060992658440192)), (61/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((-3640077431/166153499473114484112975882535043072), (-97968982161/166153499473114484112975882535043072)), (29/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22003704435/1073741824), (9412343847/1073741824)), (5/2147483648), by norm_num⟩
  | 1 => ⟨((88973953861/68719476736), (8904153847/68719476736)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((79758618019/8796093022208), (-21134614103/8796093022208)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-3585311423/35184372088832), (32679696431/562949953421312)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((56509159469/36028797018963968), (-13875182031/9007199254740992)), (21/36028797018963968), by norm_num⟩
  | 5 => ⟨((-29108909857/1152921504606846976), (382794013/9007199254740992)), (29/1152921504606846976), by norm_num⟩
  | 6 => ⟨((6248549337/18446744073709551616), (-87596266325/73786976294838206464)), (37/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-1563894571/2361183241434822606848), (38975354073/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-4121448527/18889465931478580854784), (-68072440285/75557863725914323419136)), (107/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((30986406829/2417851639229258349412352), (28696831369/1208925819614629174706176)), (151/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-42672037339/77371252455336267181195264), (-45596724947/77371252455336267181195264)), (207/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((51741860909/2475880078570760549798248448), (8137106489/618970019642690137449562112)), (17/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-58111749289/79228162514264337593543950336), (-18276506919/79228162514264337593543950336)), (361/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-35114287451/1208925819614629174706176), (-10878364139/302231454903657293676544)), (11/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((14600249773/1208925819614629174706176), (43649490189/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 2 => ⟨((-24407264465/9671406556917033397649408), (-20172030867/19342813113834066795298816)), (15/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((13888727287/38685626227668133590597632), (15872167243/309485009821345068724781056)), (17/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((-48500038191/1237940039285380274899124224), (10525166181/2475880078570760549798248448)), (33/2475880078570760549798248448), by norm_num⟩
  | 5 => ⟨((17211746501/4951760157141521099596496896), (-25761751637/19807040628566084398385987584)), (29/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((-20396879287/79228162514264337593543950336), (14196161749/79228162514264337593543950336)), (23/158456325028528675187087900672), by norm_num⟩
  | 7 => ⟨((20181743437/1267650600228229401496703205376), (-46696115631/2535301200456458802993406410752)), (1/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((-31941066531/40564819207303340847894502572032), (64015820673/40564819207303340847894502572032)), (21/20282409603651670423947251286016), by norm_num⟩
  | 9 => ⟨((16542982105/649037107316853453566312041152512), (-38274462733/324518553658426726783156020576256)), (25/324518553658426726783156020576256), by norm_num⟩
  | 10 => ⟨((3033397859/10384593717069655257060992658440192), (81640818467/10384593717069655257060992658440192)), (57/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((-23159094845/166153499473114484112975882535043072), (-39216560115/83076749736557242056487941267521536)), (31/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((40415242889/2658455991569831745807614120560689152), (67870145557/2658455991569831745807614120560689152)), (33/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22003704435/1073741824), (9412343847/1073741824)), (11/4294967296), by norm_num⟩
  | 1 => ⟨((88973953861/68719476736), (8904153847/68719476736)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((79758618019/8796093022208), (-21134614103/8796093022208)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((-3585311423/35184372088832), (32679696431/562949953421312)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((14127289867/9007199254740992), (-13875182031/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-29108909853/1152921504606846976), (48997633663/1152921504606846976)), (15/576460752303423488), by norm_num⟩
  | 6 => ⟨((24994197329/73786976294838206464), (-10949533289/9223372036854775808)), (75/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-1563894533/2361183241434822606848), (77950708103/2361183241434822606848)), (87/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-16485794167/75557863725914323419136), (-34036220083/37778931862957161709568)), (27/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((30986406891/2417851639229258349412352), (57393662453/2417851639229258349412352)), (19/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-10668009329/19342813113834066795298816), (-45596724339/77371252455336267181195264)), (13/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((12935465141/618970019642690137449562112), (32548424787/2475880078570760549798248448)), (273/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-58111748085/79228162514264337593543950336), (-285570389/1237940039285380274899124224)), (181/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39537980357/77371252455336267181195264), (32677212201/154742504910672534362390528)), (13/77371252455336267181195264), by norm_num⟩
  | 1 => ⟨((-33748081075/154742504910672534362390528), (-602619097/19342813113834066795298816)), (25/309485009821345068724781056), by norm_num⟩
  | 2 => ⟨((58924881565/1237940039285380274899124224), (-3196874651/618970019642690137449562112)), (3/154742504910672534362390528), by norm_num⟩
  | 3 => ⟨((-34852210497/4951760157141521099596496896), (6520648491/2475880078570760549798248448)), (35/9903520314283042199192993792), by norm_num⟩
  | 4 => ⟨((61952719065/79228162514264337593543950336), (-43118891289/79228162514264337593543950336)), (39/79228162514264337593543950336), by norm_num⟩
  | 5 => ⟨((-42909491431/633825300114114700748351602688), (12410390731/158456325028528675187087900672)), (19/316912650057057350374175801344), by norm_num⟩
  | 6 => ⟨((45274414305/10141204801825835211973625643008), (-90738322225/10141204801825835211973625643008)), (35/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((-1884263841/10141204801825835211973625643008), (34876026921/40564819207303340847894502572032)), (27/40564819207303340847894502572032), by norm_num⟩
  | 8 => ⟨((-3455073495/1298074214633706907132624082305024), (-46494894693/649037107316853453566312041152512)), (39/649037107316853453566312041152512), by norm_num⟩
  | 9 => ⟨((16120172153/10384593717069655257060992658440192), (54594335793/10384593717069655257060992658440192)), (27/5192296858534827628530496329220096), by norm_num⟩
  | 10 => ⟨((-8439457725/41538374868278621028243970633760768), (-1771569287/5192296858534827628530496329220096)), (17/41538374868278621028243970633760768), by norm_num⟩
  | 11 => ⟨((51704709013/2658455991569831745807614120560689152), (25766382193/1329227995784915872903807060280344576)), (41/1329227995784915872903807060280344576), by norm_num⟩
  | 12 => ⟨((-66773065699/42535295865117307932921825928971026432), (-19730627723/21267647932558653966460912964485513216)), (93/42535295865117307932921825928971026432), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22003704435/1073741824), (9412343847/1073741824)), (3/1073741824), by norm_num⟩
  | 1 => ⟨((88973953861/68719476736), (8904153847/68719476736)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((79758618019/8796093022208), (-21134614103/8796093022208)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-3585311423/35184372088832), (32679696431/562949953421312)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((14127289867/9007199254740992), (-13875182031/9007199254740992)), (23/36028797018963968), by norm_num⟩
  | 5 => ⟨((-29108909853/1152921504606846976), (48997633663/1152921504606846976)), (31/1152921504606846976), by norm_num⟩
  | 6 => ⟨((24994197329/73786976294838206464), (-87596266313/73786976294838206464)), (19/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-1563894533/2361183241434822606848), (77950708105/2361183241434822606848)), (11/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-16485794167/75557863725914323419136), (-68072440171/75557863725914323419136)), (109/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((30986406895/2417851639229258349412352), (28696831233/1208925819614629174706176)), (153/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-10668009333/19342813113834066795298816), (-45596724365/77371252455336267181195264)), (209/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((12935465153/618970019642690137449562112), (32548424835/2475880078570760549798248448)), (137/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-58111748209/79228162514264337593543950336), (-9138252485/39614081257132168796771975168)), (363/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-329139456582493/524288), (509681213729121/1048576)), (3430659/524288), by norm_num⟩
  | 1 => ⟨((-56051126041/64), (8767861121/16)), (303/32), by norm_num⟩
  | 2 => ⟨((-77695150683/128), (38902995031/128)), (221/32), by norm_num⟩
  | 3 => ⟨((-71545377307/256), (28053263677/256)), (217/64), by norm_num⟩
  | 4 => ⟨((-98667940083/1024), (14564491535/512)), (645/512), by norm_num⟩
  | 5 => ⟨((-108832668981/4096), (22516421247/4096)), (775/2048), by norm_num⟩
  | 6 => ⟨((-100107536747/16384), (3124392209/4096)), (1567/16384), by norm_num⟩
  | 7 => ⟨((-2469832651/2048), (3745535429/65536)), (343/16384), by norm_num⟩
  | 8 => ⟨((-109394031951/524288), (-731915767/131072)), (1061/262144), by norm_num⟩
  | 9 => ⟨((-67438534247/2097152), (-6653775665/2097152)), (737/1048576), by norm_num⟩
  | 10 => ⟨((-37503495739/8388608), (-12690145015/16777216)), (1863/16777216), by norm_num⟩
  | 11 => ⟨((-76025330801/134217728), (-568016867/4194304)), (2163/134217728), by norm_num⟩
  | 12 => ⟨((-35405603201/536870912), (-1367747119/67108864)), (1163/536870912), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1610669597141895/10141204801825835211973625643008), (3234049954037/10141204801825835211973625643008)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1814198023703737/633825300114114700748351602688), (3969875569641/633825300114114700748351602688)), (2243/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((964821299031929/19807040628566084398385987584), (279879168697/2475880078570760549798248448)), (5063/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((3773343109201/4835703278458516698824704), (4768138319305/2475880078570760549798248448)), (337/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1813663051253411/154742504910672534362390528), (597442722425/19342813113834066795298816)), (2703/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1589419313475229/9671406556917033397649408), (4492972874427/9671406556917033397649408)), (5083/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((646859747481009/302231454903657293676544), (3943546999059/604462909807314587353088)), (279/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1944645151412275/75557863725914323419136), (3215611658055/37778931862957161709568)), (7283/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((670129371878921/2361183241434822606848), (605449984907/590295810358705651712)), (343/295147905179352825856), by norm_num⟩
  | 9 => ⟨((840158357097239/295147905179352825856), (6692921303823/590295810358705651712)), (7587/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1897255524677285/73786976294838206464), (4207958552755/36893488147419103232)), (9547/73786976294838206464), by norm_num⟩
  | 7 => ⟨((119120627389695/576460752303423488), (9536838754921/9223372036854775808)), (10829/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1677517529091619/1152921504606846976), (9623766737347/1152921504606846976)), (2735/288230376151711744), by norm_num⟩
  | 5 => ⟨((1268055043029783/144115188075855872), (4259824597289/72057594037927936)), (9699/144115188075855872), by norm_num⟩
  | 4 => ⟨((801311900872247/18014398509481984), (12979859716073/36028797018963968)), (3701/9007199254740992), by norm_num⟩
  | 3 => ⟨((407340610928637/2251799813685248), (16581614853401/9007199254740992)), (9481/4503599627370496), by norm_num⟩
  | 2 => ⟨((1256167946001369/2251799813685248), (17129248882093/2251799813685248)), (19667/2251799813685248), by norm_num⟩
  | 1 => ⟨((331669415637219/281474976710656), (27107532060731/1125899906842624)), (7831/281474976710656), by norm_num⟩
  | 0 => ⟨((1549645264255599/1125899906842624), (939771006463/17592186044416)), (35173/562949953421312), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1549645264255599/1125899906842624), (939771006463/17592186044416)), (134174349071311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((532414775061867/281474976710656), (5173858460417/35184372088832)), (25145/140737488355328), by norm_num⟩
  | 2 => ⟨((250246302592493/70368744177664), (9786442548449/17592186044416)), (12815/17592186044416), by norm_num⟩
  | 3 => ⟨((27129774265843/2199023255552), (278421460198299/70368744177664)), (26351/4398046511104), by norm_num⟩
  | 4 => ⟨((600560253845311/4398046511104), (858734820888713/8796093022208)), (1717433/8796093022208), by norm_num⟩
  | 5 => ⟨((39150071039951/4294967296), (458053152757583/17179869184)), (1571039/17179869184), by norm_num⟩
  | 6 => ⟨((-329139456582493/524288), (509681213729121/1048576)), (3430659/524288), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((22003704435/1073741824), (9412343847/1073741824)), (3/1073741824), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/22203241), (-5594880/22203241)), 0, by norm_num⟩
  | 1 => ⟨((13113787187200/492983910904081), (12604145664000/492983910904081)), 0, by norm_num⟩
  | 2 => ⟨((-20102375225/4398046511104), (18071166231/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-3795029639/140737488355328), (-11964536055/17592186044416)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((6126026721/70368744177664), (2188834945/70368744177664)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-2346232413/281474976710656), (42290585619/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-3423853157/4503599627370496), (-27500710561/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((66554680399/288230376151711744), (-1321481801/72057594037927936)), (9/288230376151711744), by norm_num⟩
  | 8 => ⟨((-10841683483/1152921504606846976), (34614188719/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-15244449009/4611686018427387904), (-49951901141/18446744073709551616)), (21/18446744073709551616), by norm_num⟩
  | 10 => ⟨((75096364817/147573952589676412928), (-20594453629/73786976294838206464)), (31/147573952589676412928), by norm_num⟩
  | 11 => ⟨((689875667/73786976294838206464), (92409125291/1180591620717411303424)), (45/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-97622576335/9444732965739290427392), (-26378659279/9444732965739290427392)), (1/147573952589676412928), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (4371/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (4371/1280)))⁻¹=value ((2252800/22203241), (-5594880/22203241)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/22203241), (-5594880/22203241))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/28347241), (-5594880/28347241)), 0, by norm_num⟩
  | 1 => ⟨((8080622387200/803566072312081), (21770797056000/803566072312081)), 0, by norm_num⟩
  | 2 => ⟨((-59177025705/17592186044416), (-7627338875/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((22267968433/70368744177664), (-19171485191/70368744177664)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((11634594167/2251799813685248), (112426712371/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 5 => ⟨((-47573342135/9007199254740992), (-26272797763/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((1464474707/2251799813685248), (-23132329497/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 7 => ⟨((-14938015223/1152921504606846976), (99397736379/1152921504606846976)), (31/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-35135102035/4611686018427387904), (-66370180351/9223372036854775808)), (43/9223372036854775808), by norm_num⟩
  | 9 => ⟨((90981498019/73786976294838206464), (-9517237573/36893488147419103232)), (59/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-34928492799/590295810358705651712), (41139630719/295147905179352825856)), (5/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-178825187/18446744073709551616), (-72752870433/4722366482869645213696)), (27/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((41286542775/18889465931478580854784), (1902588763/18889465931478580854784)), (145/37778931862957161709568), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (4371/1280)))⁻¹=value ((3891200/28347241), (-5594880/28347241)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/28347241), (-5594880/28347241))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-22536586854400/629400623608081), (-34374942720000/629400623608081)), 0, by norm_num⟩
  | 1 => ⟨((72765193389/4398046511104), (-1677497697/1099511627776)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-21232475195/17592186044416), (12849252553/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-6041370813/17592186044416), (-28686659029/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((92199130453/1125899906842624), (-21191997065/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-13753047541/4503599627370496), (55426984501/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-6352802571/4503599627370496), (-21717628187/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 7 => ⟨((70289184205/288230376151711744), (-15067680649/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 8 => ⟨((-4115815949/2305843009213693952), (85820922527/2305843009213693952)), (25/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-83723170541/18446744073709551616), (-11298320589/4611686018427387904)), (19/9223372036854775808), by norm_num⟩
  | 10 => ⟨((41914244009/73786976294838206464), (-30879361309/73786976294838206464)), (7/18446744073709551616), by norm_num⟩
  | 11 => ⟨((1405176415/73786976294838206464), (110597342901/1180591620717411303424)), (5/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-29566461931/2361183241434822606848), (-13664976831/4722366482869645213696)), (29/2361183241434822606848), by norm_num⟩
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
  | 0 => ⟨((27/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/4196449), (-1864960/12589347)), 0, by norm_num⟩
  | 1 => ⟨((40344780800/158491657886409), (381943808000/17610184209601)), 0, by norm_num⟩
  | 2 => ⟨((-28589095501/17592186044416), (-55199662569/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((132388759709/562949953421312), (-3108037959/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-18922553761/1125899906842624), (40133690313/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((-3235513265/36028797018963968), (-91858000075/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((7040682645/36028797018963968), (51878326309/288230376151711744)), (5/144115188075855872), by norm_num⟩
  | 7 => ⟨((-127453850271/4611686018427387904), (2993833117/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((17773453921/9223372036854775808), (-39514805495/18446744073709551616)), (15/18446744073709551616), by norm_num⟩
  | 9 => ⟨((2596948395/147573952589676412928), (88409510509/295147905179352825856)), (9/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-55428956333/2361183241434822606848), (-1521822379/73786976294838206464)), (43/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((122635154283/37778931862957161709568), (-4324942387/18889465931478580854784)), (103/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-33347150931/151115727451828646838272), (19433345109/75557863725914323419136)), (61/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (4371/1280)))⁻¹=value ((614400/4196449), (-1864960/12589347)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/4196449), (-1864960/12589347))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-58639191105/4398046511104), (-11839178009/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((29658188827/8796093022208), (-30476706465/8796093022208)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((18710910019/70368744177664), (78103713355/70368744177664)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-59769713443/281474976710656), (-9903678583/140737488355328)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((67459279609/2251799813685248), (-28669254047/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((601824023/562949953421312), (57081133373/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-67213333235/72057594037927936), (-25384300837/72057594037927936)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((66057822369/576460752303423488), (-54610566253/576460752303423488)), (5/144115188075855872), by norm_num⟩
  | 8 => ⟨((17895098549/4611686018427387904), (1523033077/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 9 => ⟨((-3316997703/1152921504606846976), (-17454534581/18446744073709551616)), (25/18446744073709551616), by norm_num⟩
  | 10 => ⟨((11137037681/36893488147419103232), (-5335761421/18446744073709551616)), (37/147573952589676412928), by norm_num⟩
  | 11 => ⟨((9439995795/590295810358705651712), (64257625805/1180591620717411303424)), (27/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-35248329011/4722366482869645213696), (-807877497/590295810358705651712)), (79/9444732965739290427392), by norm_num⟩
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
  | 0 => ⟨((35/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/50465641), (-5594880/50465641)), 0, by norm_num⟩
  | 1 => ⟨((-10038770892800/2546780921540881), (40104099840000/2546780921540881)), 0, by norm_num⟩
  | 2 => ⟨((-10431423583/17592186044416), (-94071031109/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((16355799533/140737488355328), (17471328593/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-105331618881/9007199254740992), (18319945811/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((51719873783/72057594037927936), (-57118873367/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-4054625051/576460752303423488), (13846937399/144115188075855872)), (13/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-44517300013/9223372036854775808), (-4158319615/576460752303423488)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((54797266477/73786976294838206464), (4514762995/18446744073709551616)), (15/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-19570742591/295147905179352825856), (219378029/9223372036854775808)), (31/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((32023842279/9444732965739290427392), (-6333656243/1180591620717411303424)), (33/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((8551001529/151115727451828646838272), (21494495167/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-21493041709/604462909807314587353088), (-45056266143/1208925819614629174706176)), (35/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (4371/1280)))⁻¹=value ((7168000/50465641), (-5594880/50465641)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/50465641), (-5594880/50465641))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19283000967/8796093022208), (1204859409/1099511627776)), (3/35184372088832), by norm_num⟩
  | 1 => ⟨((13351259289/70368744177664), (-74962655347/70368744177664)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((58095235455/281474976710656), (60332345695/281474976710656)), (3/140737488355328), by norm_num⟩
  | 3 => ⟨((-72622759983/1125899906842624), (10994573253/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 4 => ⟨((12321109121/2251799813685248), (-25236055731/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((19582990005/18014398509481984), (67763949095/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 6 => ⟨((-101746865589/288230376151711744), (-5747051815/288230376151711744)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((36834507011/1152921504606846976), (-51088254841/1152921504606846976)), (19/1152921504606846976), by norm_num⟩
  | 8 => ⟨((7106160325/2305843009213693952), (34541205089/4611686018427387904)), (15/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-84677928327/73786976294838206464), (-13025345081/73786976294838206464)), (23/36893488147419103232), by norm_num⟩
  | 10 => ⟨((15066572095/147573952589676412928), (-37079193527/295147905179352825856)), (71/590295810358705651712), by norm_num⟩
  | 11 => ⟨((18934229197/2361183241434822606848), (24248524741/1180591620717411303424)), (13/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-110312768347/37778931862957161709568), (-7197678643/18889465931478580854784)), (153/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((43/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/66440041), (-5594880/66440041)), 0, by norm_num⟩
  | 1 => ⟨((-23124999372800/4414279048081681), (49270751232000/4414279048081681)), 0, by norm_num⟩
  | 2 => ⟨((-8639503811/70368744177664), (-16893674221/17592186044416)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((13671130831/281474976710656), (16458533599/281474976710656)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-102336826439/18014398509481984), (-16484539815/9007199254740992)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((32681408869/72057594037927936), (-8495580569/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-14465602467/576460752303423488), (62050302847/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 7 => ⟨((19553934697/36893488147419103232), (-104776940365/36893488147419103232)), (5/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1557850625/18446744073709551616), (62137804267/295147905179352825856)), (9/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-68291161981/4722366482869645213696), (-49097448645/4722366482869645213696)), (1/147573952589676412928), by norm_num⟩
  | 10 => ⟨((105489835245/75557863725914323419136), (6055494807/75557863725914323419136)), (7/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-57968986015/604462909807314587353088), (16161213987/302231454903657293676544)), (25/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((19846945767/4835703278458516698824704), (-73326113713/9671406556917033397649408)), (11/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (4371/1280)))⁻¹=value ((8806400/66440041), (-5594880/66440041)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/66440041), (-5594880/66440041))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-27907380547/140737488355328), (46422576445/140737488355328)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((-18381796511/281474976710656), (-52744601843/281474976710656)), (5/281474976710656), by norm_num⟩
  | 2 => ⟨((64879592785/1125899906842624), (5826275095/281474976710656)), (7/1125899906842624), by norm_num⟩
  | 3 => ⟨((-13981090085/1125899906842624), (17520097175/2251799813685248)), (9/4503599627370496), by norm_num⟩
  | 4 => ⟨((9975565899/36028797018963968), (-107535380085/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((29528633547/72057594037927936), (13230475215/36028797018963968)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((-105018072701/1152921504606846976), (11529720791/576460752303423488)), (31/1152921504606846976), by norm_num⟩
  | 7 => ⟨((3284577449/576460752303423488), (-31646739787/2305843009213693952)), (27/4611686018427387904), by norm_num⟩
  | 8 => ⟨((45728060669/36893488147419103232), (34730174589/18446744073709551616)), (43/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-96923772975/295147905179352825856), (96443101/147573952589676412928)), (67/295147905179352825856), by norm_num⟩
  | 10 => ⟨((29147847895/1180591620717411303424), (-46183793995/1180591620717411303424)), (13/295147905179352825856), by norm_num⟩
  | 11 => ⟨((13238485083/4722366482869645213696), (53638820059/9444732965739290427392)), (77/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-15943230401/18889465931478580854784), (-2378737865/37778931862957161709568)), (113/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((51/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/28563747), (-1864960/28563747)), 0, by norm_num⟩
  | 1 => ⟨((-1440577126400/271962547560003), (6493044736000/815887642680009)), 0, by norm_num⟩
  | 2 => ⟨((8869074913/140737488355328), (-5787246655/8796093022208)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((77572743/4398046511104), (94923825565/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-11038772185/4503599627370496), (-17953927329/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((61811797893/288230376151711744), (11950620479/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-4157216921/288230376151711744), (20632937363/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((54082725225/73786976294838206464), (-13715590397/18446744073709551616)), (11/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-24080399893/1180591620717411303424), (10218229329/147573952589676412928)), (9/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-600537383/590295810358705651712), (-92289090907/18889465931478580854784)), (7/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((33472086623/151115727451828646838272), (9994290895/37778931862957161709568)), (11/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-26760106477/1208925819614629174706176), (-21498689245/2417851639229258349412352)), (17/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((63417497407/38685626227668133590597632), (-6991581287/38685626227668133590597632)), (13/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (4371/1280)))⁻¹=value ((3481600/28563747), (-1864960/28563747)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/28563747), (-1864960/28563747))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5929803507/2251799813685248), (59843966711/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 1 => ⟨((-12255054329/562949953421312), (-1541198033/70368744177664)), (9/2251799813685248), by norm_num⟩
  | 2 => ⟨((5864238485/562949953421312), (-5541937737/9007199254740992)), (7/4503599627370496), by norm_num⟩
  | 3 => ⟨((-7297416193/4503599627370496), (76982230415/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 4 => ⟨((-19041746247/144115188075855872), (-81424532237/144115188075855872)), (21/144115188075855872), by norm_num⟩
  | 5 => ⟨((57889551959/576460752303423488), (6935407577/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 6 => ⟨((-5040578891/288230376151711744), (10065720559/1152921504606846976)), (35/4611686018427387904), by norm_num⟩
  | 7 => ⟨((10684140903/18446744073709551616), (-58068134047/18446744073709551616)), (31/18446744073709551616), by norm_num⟩
  | 8 => ⟨((25195884219/73786976294838206464), (13256232055/36893488147419103232)), (25/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-85622300753/1180591620717411303424), (12715076159/1180591620717411303424)), (39/590295810358705651712), by norm_num⟩
  | 10 => ⟨((21362038491/4722366482869645213696), (-44409937557/4722366482869645213696)), (15/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((28100677005/37778931862957161709568), (46468330859/37778931862957161709568)), (91/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-116343615891/604462909807314587353088), (-981269265/302231454903657293676544)), (269/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((59/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/108219241), (-5594880/108219241)), 0, by norm_num⟩
  | 1 => ⟨((-57350520012800/11711404122616081), (67604054016000/11711404122616081)), 0, by norm_num⟩
  | 2 => ⟨((2184389123/17592186044416), (-15792481295/35184372088832)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((10517380419/2251799813685248), (15913362395/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1116291841/1125899906842624), (-52507770267/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((53624678891/576460752303423488), (16063882209/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-122375089519/18446744073709551616), (-13037616419/18446744073709551616)), (17/18446744073709551616), by norm_num⟩
  | 7 => ⟨((28675613813/73786976294838206464), (-19484069903/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-5396224509/295147905179352825856), (41124158309/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((5388035369/9444732965739290427392), (-54588537233/37778931862957161709568)), (11/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((3326394005/604462909807314587353088), (115348930735/1208925819614629174706176)), (29/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-6706297207/2417851639229258349412352), (-25070636917/4835703278458516698824704)), (39/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((44699521173/154742504910672534362390528), (2105833137/9671406556917033397649408)), (13/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (4371/1280)))⁻¹=value ((12083200/108219241), (-5594880/108219241)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/108219241), (-5594880/108219241))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5525714445/2251799813685248), (6835151321/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-34739747447/9007199254740992), (-14370595805/9007199254740992)), (13/18014398509481984), by norm_num⟩
  | 2 => ⟨((50002876087/36028797018963968), (-2782687597/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 3 => ⟨((-9508936343/72057594037927936), (28297965213/72057594037927936)), (15/144115188075855872), by norm_num⟩
  | 4 => ⟨((-26947927131/576460752303423488), (-47032817527/576460752303423488)), (9/288230376151711744), by norm_num⟩
  | 5 => ⟨((84944761971/4611686018427387904), (16269996347/4611686018427387904)), (9/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-3021532427/1152921504606846976), (19905119609/9223372036854775808)), (33/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-139292615/18446744073709551616), (-84065183609/147573952589676412928)), (29/73786976294838206464), by norm_num⟩
  | 8 => ⟨((21206240693/295147905179352825856), (31918384151/590295810358705651712)), (3/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-61154008033/4722366482869645213696), (8950383061/2361183241434822606848)), (75/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((24324343417/37778931862957161709568), (-34572637087/18889465931478580854784)), (117/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((2984693997/18889465931478580854784), (65796816991/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-43651075221/1208925819614629174706176), (459081029/302231454903657293676544)), (265/2417851639229258349412352), by norm_num⟩
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
  | 0 => ⟨((67/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/134024041), (-5594880/134024041)), 0, by norm_num⟩
  | 1 => ⟨((-78489812172800/17962443565969681), (76770705408000/17962443565969681)), 0, by norm_num⟩
  | 2 => ⟨((37852100929/281474976710656), (-87255514833/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-465696349/1125899906842624), (42054044163/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-3320406263/9007199254740992), (-17377771881/18014398509481984)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((22485413225/576460752303423488), (48062131887/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-52884455419/18446744073709551616), (-12173427047/9223372036854775808)), (5/18446744073709551616), by norm_num⟩
  | 7 => ⟨((25723058761/147573952589676412928), (4559851909/590295810358705651712)), (13/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-85797020051/9444732965739290427392), (15313707607/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 9 => ⟨((60043894811/151115727451828646838272), (-26869244217/75557863725914323419136)), (19/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-31232480917/2417851639229258349412352), (64067098475/2417851639229258349412352)), (11/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((8370066351/77371252455336267181195264), (-125809676939/77371252455336267181195264)), (13/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((17580109911/618970019642690137449562112), (26460022645/309485009821345068724781056)), (31/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (4371/1280)))⁻¹=value ((13721600/134024041), (-5594880/134024041)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/134024041), (-5594880/134024041))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((36364901709/72057594037927936), (37405280863/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 1 => ⟨((-35895237389/72057594037927936), (-1324272217/72057594037927936)), (17/144115188075855872), by norm_num⟩
  | 2 => ⟨((40981086217/288230376151711744), (-9414551281/72057594037927936)), (17/288230376151711744), by norm_num⟩
  | 3 => ⟨((-3846048619/2305843009213693952), (127677774615/2305843009213693952)), (43/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-21357590103/2305843009213693952), (-42755181931/4611686018427387904)), (27/4611686018427387904), by norm_num⟩
  | 5 => ⟨((99640158591/36893488147419103232), (-2332828317/18446744073709551616)), (55/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-46314693119/147573952589676412928), (14506587085/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-19709570535/1180591620717411303424), (-49989358715/590295810358705651712)), (91/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((57780712707/4722366482869645213696), (15402531487/2361183241434822606848)), (77/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-36458397113/18889465931478580854784), (32117652073/37778931862957161709568)), (123/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((10664645943/151115727451828646838272), (-90085850839/302231454903657293676544)), (3/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((16848850075/604462909807314587353088), (19599199337/604462909807314587353088)), (147/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-110969575109/19342813113834066795298816), (11311970921/19342813113834066795298816)), (441/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((75/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/54368547), (-1864960/54368547)), 0, by norm_num⟩
  | 1 => ⟨((-3789387366400/985312967630403), (9548595200000/2955938902891209)), 0, by norm_num⟩
  | 2 => ⟨((17688391213/140737488355328), (-61379383421/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-2452117439/1125899906842624), (55949808961/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((-15928265457/144115188075855872), (-22421450817/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((36611337773/2305843009213693952), (7899525709/288230376151711744)), (5/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-22462137539/18446744073709551616), (-37563761643/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 7 => ⟨((88306116053/1180591620717411303424), (15971658549/590295810358705651712)), (13/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-75293580731/18889465931478580854784), (41847381/4722366482869645213696)), (7/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((28339249793/151115727451828646838272), (-20787982535/302231454903657293676544)), (1/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-9248919673/1208925819614629174706176), (62429508787/9671406556917033397649408)), (17/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((9652905129/38685626227668133590597632), (-67337463605/154742504910672534362390528)), (9/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-10610520221/2475880078570760549798248448), (61326184267/2475880078570760549798248448)), (19/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (4371/1280)))⁻¹=value ((5120000/54368547), (-1864960/54368547)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/54368547), (-1864960/54368547))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37661135119/576460752303423488), (2275138067/72057594037927936)), (21/1152921504606846976), by norm_num⟩
  | 1 => ⟨((-58983048159/1152921504606846976), (17283032891/1152921504606846976)), (5/288230376151711744), by norm_num⟩
  | 2 => ⟨((25501839569/2305843009213693952), (-43267570277/2305843009213693952)), (5/576460752303423488), by norm_num⟩
  | 3 => ⟨((3558741569/2305843009213693952), (58521179029/9223372036854775808)), (27/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-6326159463/4611686018427387904), (-3816813929/4611686018427387904)), (17/18446744073709551616), by norm_num⟩
  | 5 => ⟨((24259942647/73786976294838206464), (-26300038553/295147905179352825856)), (9/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-35441548445/1180591620717411303424), (68036076163/1180591620717411303424)), (35/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-19134682873/4722366482869645213696), (-25101070391/2361183241434822606848)), (31/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((66080079675/37778931862957161709568), (5909224529/9444732965739290427392)), (107/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-74254960501/302231454903657293676544), (44369355935/302231454903657293676544)), (173/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((6615488763/1208925819614629174706176), (-50311784073/1208925819614629174706176)), (17/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((40555029221/9671406556917033397649408), (10035873003/2417851639229258349412352)), (105/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-61033494807/77371252455336267181195264), (2482500371/19342813113834066795298816)), (79/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((83/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/195464041), (-5594880/195464041)), 0, by norm_num⟩
  | 1 => ⟨((-128821460172800/38206191324049681), (95104008192000/38206191324049681)), 0, by norm_num⟩
  | 2 => ⟨((31239600545/281474976710656), (-44048806913/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-11647172979/4503599627370496), (75597827693/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((-2209647461/288230376151711744), (-115857314917/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((28067290207/4611686018427387904), (5006103065/288230376151711744)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-18934137569/36893488147419103232), (-49298019243/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((75268399061/2361183241434822606848), (12812975561/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-4006339451/2361183241434822606848), (-18421093609/37778931862957161709568)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((24407263259/302231454903657293676544), (-465668239/151115727451828646838272)), (31/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-67068902225/19342813113834066795298816), (12473859705/9671406556917033397649408)), (29/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((639813675/4835703278458516698824704), (-2044656831/19342813113834066795298816)), (7/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-41993852585/9903520314283042199192993792), (32136606929/4951760157141521099596496896)), (53/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (4371/1280)))⁻¹=value ((16998400/195464041), (-5594880/195464041)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/195464041), (-5594880/195464041))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((30369249757/4611686018427387904), (4038804199/4611686018427387904)), (5/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-79668800933/18446744073709551616), (52097101185/18446744073709551616)), (5/2305843009213693952), by norm_num⟩
  | 2 => ⟨((1319099025/2305843009213693952), (-78694023961/36893488147419103232)), (21/18446744073709551616), by norm_num⟩
  | 3 => ⟨((47442459801/147573952589676412928), (22451043977/36893488147419103232)), (59/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-12224497359/73786976294838206464), (-32212293735/590295810358705651712)), (19/147573952589676412928), by norm_num⟩
  | 5 => ⟨((40171584255/1180591620717411303424), (-20257112665/1180591620717411303424)), (83/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-5183093569/2361183241434822606848), (67095409993/9444732965739290427392)), (41/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-12521532611/18889465931478580854784), (-86802851371/75557863725914323419136)), (37/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((65066091173/302231454903657293676544), (846447909/18889465931478580854784)), (129/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-65684520105/2417851639229258349412352), (25305279723/1208925819614629174706176)), (53/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((3217554651/19342813113834066795298816), (-49080396595/9671406556917033397649408)), (21/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((21233466133/38685626227668133590597632), (35898947879/77371252455336267181195264)), (261/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-59070699143/618970019642690137449562112), (414341651/19342813113834066795298816)), (395/618970019642690137449562112), by norm_num⟩
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
  | 0 => ⟨((91/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/231099241), (-5594880/231099241)), 0, by norm_num⟩
  | 1 => ⟨((-158013816012800/53406859190776081), (104270659584000/53406859190776081)), 0, by norm_num⟩
  | 2 => ⟨((3365971027/35184372088832), (-64479585385/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-11128367465/4503599627370496), (1625933943/281474976710656)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((2140956369/72057594037927936), (-2367368969/9007199254740992)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((9147320285/4611686018427387904), (101065456977/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-15688544149/73786976294838206464), (-7707426395/18446744073709551616)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((32185152023/2361183241434822606848), (33702683433/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-54583698833/75557863725914323419136), (-15509808005/37778931862957161709568)), (13/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((41222688659/1208925819614629174706176), (4720346697/604462909807314587353088)), (23/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-113693638747/77371252455336267181195264), (1893270837/19342813113834066795298816)), (39/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((35941530661/618970019642690137449562112), (-26905854019/1237940039285380274899124224)), (17/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-41164486999/19807040628566084398385987584), (1955039139/1237940039285380274899124224)), (15/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (4371/1280)))⁻¹=value ((18636800/231099241), (-5594880/231099241)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/231099241), (-5594880/231099241))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((20375047747/36893488147419103232), (-3276234801/36893488147419103232)), (35/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-44436091145/147573952589676412928), (25277871965/73786976294838206464)), (9/36893488147419103232), by norm_num⟩
  | 2 => ⟨((1469054581/590295810358705651712), (-30005109079/147573952589676412928)), (39/295147905179352825856), by norm_num⟩
  | 3 => ⟨((50788030249/1180591620717411303424), (29231677183/590295810358705651712)), (29/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-80354516459/4722366482869645213696), (-8811159587/4722366482869645213696)), (75/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((57373773619/18889465931478580854784), (-11042064961/4722366482869645213696)), (21/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-7495695863/75557863725914323419136), (57204081741/75557863725914323419136)), (85/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-26123388731/302231454903657293676544), (-32739540943/302231454903657293676544)), (39/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((112395779375/4835703278458516698824704), (4166723847/2417851639229258349412352)), (275/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-25553001841/9671406556917033397649408), (24735674613/9671406556917033397649408)), (229/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-2620517175/77371252455336267181195264), (-2651852827/4835703278458516698824704)), (183/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((4913090315/77371252455336267181195264), (56736822491/1237940039285380274899124224)), (573/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-6370954383/618970019642690137449562112), (14650050789/4951760157141521099596496896)), (873/9903520314283042199192993792), by norm_num⟩
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
  | 0 => ⟨((99/8), (4371/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/30001249), (-1864960/90003747)), 0, by norm_num⟩
  | 1 => ⟨((-21098947379200/8100674474040009), (4201381888000/2700224824680003)), 0, by norm_num⟩
  | 2 => ⟨((5746975061/70368744177664), (-24038696263/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-39297996969/18014398509481984), (73004832303/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((23010684773/576460752303423488), (-3148119217/18014398509481984)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((1438176271/4611686018427387904), (64331008085/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-12391866117/147573952589676412928), (-76336448989/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 7 => ⟨((27542213311/4722366482869645213696), (20874312603/2361183241434822606848)), (3/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-46931523507/151115727451828646838272), (-41027408773/151115727451828646838272)), (5/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((69987572359/4835703278458516698824704), (33732680107/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-95269652829/154742504910672534362390528), (-17324598237/154742504910672534362390528)), (25/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((120204791813/4951760157141521099596496896), (-10770667495/4951760157141521099596496896)), (39/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-35212098489/39614081257132168796771975168), (1649762469/4951760157141521099596496896)), (31/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (4371/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (4371/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (4371/1280)))⁻¹=value ((2252800/30001249), (-1864960/90003747)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/30001249), (-1864960/90003747))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((93573118169/2361183241434822606848), (-42764978183/2361183241434822606848)), (27/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-4962076475/295147905179352825856), (78047039893/2361183241434822606848)), (59/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((-2206169069/590295810358705651712), (-19756378771/1180591620717411303424)), (33/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((43163557811/9444732965739290427392), (32269538941/9444732965739290427392)), (51/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-115101860607/75557863725914323419136), (9939245265/75557863725914323419136)), (133/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((555954477/2361183241434822606848), (-19587441413/75557863725914323419136)), (77/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((2519274125/1208925819614629174706176), (42964117643/604462909807314587353088)), (79/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-1443107239/151115727451828646838272), (-21737114429/2417851639229258349412352)), (147/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((43186893821/19342813113834066795298816), (-4395029649/38685626227668133590597632)), (131/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-35289263307/154742504910672534362390528), (21214875691/77371252455336267181195264)), (221/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((-10132520807/1237940039285380274899124224), (-32888579955/618970019642690137449562112)), (357/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((32561385615/4951760157141521099596496896), (39969222727/9903520314283042199192993792)), (561/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-79250849993/79228162514264337593543950336), (13945583495/39614081257132168796771975168)), (431/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-35350126865/2199023255552), (67362776513/2199023255552)), (111/274877906944), by norm_num⟩
  | 1 => ⟨((-8327400071/274877906944), (9517552643/1099511627776)), (1027/1099511627776), by norm_num⟩
  | 2 => ⟨((-50398747305/4398046511104), (-14149721389/2199023255552)), (4737/4398046511104), by norm_num⟩
  | 3 => ⟨((-8957630997/8796093022208), (-105986599/34359738368)), (7423/8796093022208), by norm_num⟩
  | 4 => ⟨((5111182517/35184372088832), (-69934388687/140737488355328)), (71019/140737488355328), by norm_num⟩
  | 5 => ⟨((36436564093/1125899906842624), (-61430757075/1125899906842624)), (138165/562949953421312), by norm_num⟩
  | 6 => ⟨((52824680145/9007199254740992), (-73068580369/9007199254740992)), (910923/9007199254740992), by norm_num⟩
  | 7 => ⟨((5790501419/4503599627370496), (-24708846581/36028797018963968)), (1308561/36028797018963968), by norm_num⟩
  | 8 => ⟨((4559622015/36028797018963968), (773697851/576460752303423488)), (6692553/576460752303423488), by norm_num⟩
  | 9 => ⟨((81212520911/9223372036854775808), (-13701776809/4611686018427387904)), (30959667/9223372036854775808), by norm_num⟩
  | 10 => ⟨((66137266261/36893488147419103232), (-8982512357/36893488147419103232)), (32809679/36893488147419103232), by norm_num⟩
  | 11 => ⟨((2292921229/18446744073709551616), (9523450661/73786976294838206464)), (64393745/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-88874921791/18889465931478580854784), (3718402715/2361183241434822606848)), (944629607/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-35350126865/2199023255552), (67362776513/2199023255552)), (889/2199023255552), by norm_num⟩
  | 1 => ⟨((-8327400071/274877906944), (9517552643/1099511627776)), (2055/2199023255552), by norm_num⟩
  | 2 => ⟨((-50398747305/4398046511104), (-14149721389/2199023255552)), (2369/2199023255552), by norm_num⟩
  | 3 => ⟨((-8957630997/8796093022208), (-105986599/34359738368)), (14847/17592186044416), by norm_num⟩
  | 4 => ⟨((5111182517/35184372088832), (-69934388687/140737488355328)), (71025/140737488355328), by norm_num⟩
  | 5 => ⟨((36436564093/1125899906842624), (-61430757075/1125899906842624)), (34547/140737488355328), by norm_num⟩
  | 6 => ⟨((52824680145/9007199254740992), (-73068580369/9007199254740992)), (227821/2251799813685248), by norm_num⟩
  | 7 => ⟨((5790501419/4503599627370496), (-24708846581/36028797018963968)), (1310003/36028797018963968), by norm_num⟩
  | 8 => ⟨((4559622015/36028797018963968), (773697851/576460752303423488)), (1678903/144115188075855872), by norm_num⟩
  | 9 => ⟨((81212520911/9223372036854775808), (-13701776809/4611686018427387904)), (15664301/4611686018427387904), by norm_num⟩
  | 10 => ⟨((66137266261/36893488147419103232), (-8982512357/36893488147419103232)), (34285419/36893488147419103232), by norm_num⟩
  | 11 => ⟨((2292921229/18446744073709551616), (9523450661/73786976294838206464)), (38099831/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-88874921791/18889465931478580854784), (3718402715/2361183241434822606848)), (1700208245/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile015Gamma
