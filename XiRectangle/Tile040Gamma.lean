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
namespace Reinmann.XiRectangle.Tile040Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨40,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((19/32), (7191/512))
  have he : value ((19/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((83/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((851/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((13942784/237105937), (-7363584/237105937)), 0, by norm_num⟩
  | 1 => ⟨((-70089428172800/56219225360647969), (102668861177856/56219225360647969)), 0, by norm_num⟩
  | 2 => ⟨((36496269/4398046511104), (-642587255/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((501247817/562949953421312), (1281714609/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-277121753/4503599627370496), (-478425457/9007199254740992)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((759196411/288230376151711744), (349462587/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1602248889/18446744073709551616), (26605541/1152921504606846976)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((80998461/36893488147419103232), (-598334381/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-156178861/4722366482869645213696), (442467497/4722366482869645213696)), (15/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-145835701/302231454903657293676544), (-3858647/1180591620717411303424)), (11/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((628053735/9671406556917033397649408), (214233331/2417851639229258349412352)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-508360719/154742504910672534362390528), (-61772471/38685626227668133590597632)), (47/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((4695913/38685626227668133590597632), (-40250157/9903520314283042199192993792)), (17/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((851/64), (7191/1024)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((851/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((851/64), (7191/1024)))⁻¹=value ((13942784/237105937), (-7363584/237105937)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((13942784/237105937), (-7363584/237105937))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((727604233/268435456), (130431849/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((6971392/237105937), (-3681792/237105937)), 0, by norm_num⟩
  | 2 => ⟨((-17522357043200/56219225360647969), (25667215294464/56219225360647969)), 0, by norm_num⟩
  | 3 => ⟨((12165423/8796093022208), (-1713566013/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((501247817/4503599627370496), (1281714609/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((-443394805/72057594037927936), (-765480731/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 6 => ⟨((1012261881/4611686018427387904), (116487529/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-457785397/73786976294838206464), (243250661/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 8 => ⟨((80998461/590295810358705651712), (-598334381/4722366482869645213696)), (5/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-555302617/302231454903657293676544), (1573217767/302231454903657293676544)), (27/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-116668561/4835703278458516698824704), (-1580501811/9671406556917033397649408)), (9/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((456766353/154742504910672534362390528), (155806059/38685626227668133590597632)), (3/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-169453573/1237940039285380274899124224), (-658906357/9903520314283042199192993792)), (63/9903520314283042199192993792), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-28043/1106944), (153/16384)), 0, by norm_num⟩
  | 45 => ⟨((292546957381/13058042757120), (-2449683/192937984)), 0, by norm_num⟩
  | 44 => ⟨((-133909506936551/6395034505052160), (6058213882517/505775348776960)), 0, by norm_num⟩
  | 43 => ⟨((739979593/34359738368), (-192656983/17179869184)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-773989325/34359738368), (194938425/17179869184)), (1/34359738368), by norm_num⟩
  | 41 => ⟨((797685833/34359738368), (-405574729/34359738368)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-50984403/2147483648), (418627299/34359738368)), (3/34359738368), by norm_num⟩
  | 39 => ⟨((835099031/34359738368), (-214380549/17179869184)), (3/34359738368), by norm_num⟩
  | 38 => ⟨((-857104829/34359738368), (438965323/34359738368)), (3/34359738368), by norm_num⟩
  | 37 => ⟨((880781869/34359738368), (-450347707/34359738368)), (3/34359738368), by norm_num⟩
  | 36 => ⟨((-905581821/34359738368), (462662651/34359738368)), (3/34359738368), by norm_num⟩
  | 35 => ⟨((931636215/34359738368), (-118906999/8589934592)), (3/34359738368), by norm_num⟩
  | 34 => ⟨((-959221173/34359738368), (489253803/34359738368)), (3/34359738368), by norm_num⟩
  | 33 => ⟨((247131189/8589934592), (-503662963/34359738368)), (3/34359738368), by norm_num⟩
  | 32 => ⟨((-1019688855/34359738368), (518958777/34359738368)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((526438663/17179869184), (-535220975/34359738368)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-1088292777/34359738368), (552534943/34359738368)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((1126170837/34359738368), (-571004033/34359738368)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-145847369/4294967296), (147687281/8589934592)), (1/17179869184), by norm_num⟩
  | 27 => ⟨((1210422697/34359738368), (-611908021/34359738368)), (1/17179869184), by norm_num⟩
  | 26 => ⟨((-1257454879/34359738368), (158659531/8589934592)), (3/34359738368), by norm_num⟩
  | 25 => ⟨((1308285553/34359738368), (-82390109/4294967296)), (3/34359738368), by norm_num⟩
  | 24 => ⟨((-170424227/4294967296), (342783447/17179869184)), (3/34359738368), by norm_num⟩
  | 23 => ⟨((711671371/17179869184), (-178555513/8589934592)), (3/34359738368), by norm_num⟩
  | 22 => ⟨((-744399297/17179869184), (372687509/17179869184)), (1/8589934592), by norm_num⟩
  | 21 => ⟨((390138907/8589934592), (-194841747/8589934592)), (1/8589934592), by norm_num⟩
  | 20 => ⟨((-819784169/17179869184), (51037763/2147483648)), (1/8589934592), by norm_num⟩
  | 19 => ⟨((863496985/17179869184), (-428787121/17179869184)), (3/17179869184), by norm_num⟩
  | 18 => ⟨((-228031161/4294967296), (225716845/8589934592)), (3/17179869184), by norm_num⟩
  | 17 => ⟨((966543757/17179869184), (-238301293/8589934592)), (3/17179869184), by norm_num⟩
  | 16 => ⟨((-1027852171/17179869184), (504739509/17179869184)), (1/8589934592), by norm_num⟩
  | 15 => ⟨((548721663/8589934592), (-536401607/17179869184)), (1/8589934592), by norm_num⟩
  | 14 => ⟨((-1177112711/17179869184), (572294593/17179869184)), (3/17179869184), by norm_num⟩
  | 13 => ⟨((1269213797/17179869184), (-613325741/17179869184)), (3/17179869184), by norm_num⟩
  | 12 => ⟨((-1376892483/17179869184), (330340639/8589934592)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((376112573/4294967296), (-89492795/2147483648)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-828963457/8589934592), (195316017/4294967296)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((230759195/2147483648), (-214915335/4294967296)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((-1041030243/8589934592), (477742235/8589934592)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((596663903/4294967296), (-268812225/4294967296)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-698648743/4294967296), (307292625/4294967296)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((421077493/2147483648), (-358555243/4294967296)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((-264662175/1073741824), (215100629/2147483648)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((710846265/2147483648), (-67165679/536870912)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-1075918879/2147483648), (44672805/268435456)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((1086199293/1073741824), (-266301491/1073741824)), (1/536870912), by norm_num⟩
  | 0 => ⟨((-133255081/2147483648), (521727395/1073741824)), (1/536870912), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-173/1024), (7191/16384)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-173/1024), (7191/16384)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-173/1024), (7191/16384))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((727604233/268435456), (130431849/268435456)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((851/64), (7191/1024))) (z:=((-173/1024), (7191/16384))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((727604233/268435456), (130431849/268435456))) (r:=(1/268435456)) (by norm_num) ?_ hs
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
  | 0 => ⟨((819/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((524694241/16777216), (423668273/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((494073573/268435456), (134600127/536870912)), (1/268435456), by norm_num⟩
  | 2 => ⟨((422000786610176/56219225360647969), (-231077293147008/56219225360647969)), 0, by norm_num⟩
  | 3 => ⟨((-463009091/8796093022208), (722866869/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((131990793/1125899906842624), (-1873780339/1125899906842624)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((511846953/36028797018963968), (280264195/9007199254740992)), (19/18014398509481984), by norm_num⟩
  | 6 => ⟨((-717725811/1152921504606846976), (-539442371/1152921504606846976)), (51/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1385763413/73786976294838206464), (205444547/73786976294838206464)), (1/576460752303423488), by norm_num⟩
  | 8 => ⟨((-134695965/295147905179352825856), (392834261/2361183241434822606848)), (165/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((645401881/75557863725914323419136), (-182126251/18889465931478580854784)), (107/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-385907813/4835703278458516698824704), (1653699667/4835703278458516698824704)), (287/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-398082905/154742504910672534362390528), (-1461067971/154742504910672534362390528)), (765/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((947928957/4951760157141521099596496896), (248923061/1237940039285380274899124224)), (1009/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-851/64), (-7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((301609697/16777216), (305850929/16777216)), (1/8388608), by norm_num⟩
  | 1 => ⟨((359855845/268435456), (134600127/536870912)), (1/268435456), by norm_num⟩
  | 2 => ⟨((422000786610176/56219225360647969), (-231077293147008/56219225360647969)), 0, by norm_num⟩
  | 3 => ⟨((-463009091/8796093022208), (722866869/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((131990793/1125899906842624), (-1873780339/1125899906842624)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((511846953/36028797018963968), (280264195/9007199254740992)), (19/18014398509481984), by norm_num⟩
  | 6 => ⟨((-717725811/1152921504606846976), (-539442371/1152921504606846976)), (51/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1385763413/73786976294838206464), (205444547/73786976294838206464)), (1/576460752303423488), by norm_num⟩
  | 8 => ⟨((-134695965/295147905179352825856), (392834261/2361183241434822606848)), (165/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((645401881/75557863725914323419136), (-182126251/18889465931478580854784)), (107/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-385907813/4835703278458516698824704), (1653699667/4835703278458516698824704)), (287/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-398082905/154742504910672534362390528), (-1461067971/154742504910672534362390528)), (765/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((947928957/4951760157141521099596496896), (248923061/1237940039285380274899124224)), (1009/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((634053855/33554432), (305850929/16777216)), (5/33554432), by norm_num⟩
  | 1 => ⟨((359855845/268435456), (134600127/536870912)), (1/268435456), by norm_num⟩
  | 2 => ⟨((422000786610176/56219225360647969), (-231077293147008/56219225360647969)), 0, by norm_num⟩
  | 3 => ⟨((-463009091/8796093022208), (722866869/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((131990793/1125899906842624), (-1873780339/1125899906842624)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((511846953/36028797018963968), (280264195/9007199254740992)), (19/18014398509481984), by norm_num⟩
  | 6 => ⟨((-717725811/1152921504606846976), (-539442371/1152921504606846976)), (51/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1385763413/73786976294838206464), (205444547/73786976294838206464)), (1/576460752303423488), by norm_num⟩
  | 8 => ⟨((-134695965/295147905179352825856), (392834261/2361183241434822606848)), (165/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((645401881/75557863725914323419136), (-182126251/18889465931478580854784)), (107/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-385907813/4835703278458516698824704), (1653699667/4835703278458516698824704)), (287/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-398082905/154742504910672534362390528), (-1461067971/154742504910672534362390528)), (765/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((947928957/4951760157141521099596496896), (248923061/1237940039285380274899124224)), (1009/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((140178856345600/56219225360647969), (-205337722355712/56219225360647969)), 0, by norm_num⟩
  | 1 => ⟨((-36496269/1099511627776), (642587255/2199023255552)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-375935863/70368744177664), (-961285957/70368744177664)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((277121753/562949953421312), (956850915/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-474497757/18014398509481984), (-218414117/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((1201686667/1152921504606846976), (-79816623/288230376151711744)), (7/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-566989227/18446744073709551616), (523542583/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((156178861/295147905179352825856), (-442467497/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((41016291/4722366482869645213696), (34727823/590295810358705651712)), (1/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-785067169/604462909807314587353088), (-535583327/302231454903657293676544)), (3/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1397991977/19342813113834066795298816), (169874295/4835703278458516698824704)), (19/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-1803230591/618970019642690137449562112), (60375237/618970019642690137449562112)), (7/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((225684771/2475880078570760549798248448), (-516113899/9903520314283042199192993792)), (21/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((36496269/1099511627776), (-642587255/2199023255552)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((375935863/35184372088832), (961285957/35184372088832)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-831365259/562949953421312), (-358819093/281474976710656)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((474497757/4503599627370496), (218414117/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-751054167/144115188075855872), (199541557/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((850483841/4611686018427387904), (-785313875/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-273313007/73786976294838206464), (1548636239/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-41016291/590295810358705651712), (-34727823/73786976294838206464)), (13/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((883200565/75557863725914323419136), (602531243/37778931862957161709568)), (21/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-436872493/604462909807314587353088), (-424685737/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((1239721031/38685626227668133590597632), (-5188497/4835703278458516698824704)), (7/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-677054313/618970019642690137449562112), (774170849/1237940039285380274899124224)), (43/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((16212093/618970019642690137449562112), (-817391745/19807040628566084398385987584)), (33/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-501247817/70368744177664), (-1281714609/70368744177664)), (3/70368744177664), by norm_num⟩
  | 1 => ⟨((1108487013/562949953421312), (956850915/562949953421312)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((-474497757/2251799813685248), (-218414117/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((250351389/18014398509481984), (-133027705/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((-708736535/1152921504606846976), (654428229/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | 5 => ⟨((273313007/18446744073709551616), (-96789765/2305843009213693952)), (13/36893488147419103232), by norm_num⟩
  | 6 => ⟨((95704679/295147905179352825856), (81031587/36893488147419103232)), (7/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-588800377/9444732965739290427392), (-803374991/9444732965739290427392)), (13/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1310617479/302231454903657293676544), (318514303/151115727451828646838272)), (11/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-2066201719/9671406556917033397649408), (69179959/9671406556917033397649408)), (19/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((19394785/2417851639229258349412352), (-177414153/38685626227668133590597632)), (1/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-16212093/77371252455336267181195264), (408695873/1237940039285380274899124224)), (27/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((102435391/79228162514264337593543950336), (-1283548461/79228162514264337593543950336)), (21/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-277121753/281474976710656), (-478425457/562949953421312)), (5/1125899906842624), by norm_num⟩
  | 1 => ⟨((948995515/4503599627370496), (218414117/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 2 => ⟨((-751054167/36028797018963968), (399083115/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 3 => ⟨((354368267/288230376151711744), (-327214115/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((-341641259/9223372036854775808), (483948825/4611686018427387904)), (9/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-71778509/73786976294838206464), (-243094761/36893488147419103232)), (11/147573952589676412928), by norm_num⟩
  | 6 => ⟨((257600165/1180591620717411303424), (702953117/2361183241434822606848)), (11/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-1310617479/75557863725914323419136), (-318514303/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((1162238467/1208925819614629174706176), (-38913727/1208925819614629174706176)), (21/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-96973925/2417851639229258349412352), (443535383/19342813113834066795298816)), (19/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((178333023/154742504910672534362390528), (-561956825/309485009821345068724781056)), (1/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-76826543/9903520314283042199192993792), (481330673/4951760157141521099596496896)), (55/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-541414187/316912650057057350374175801344), (-1258544989/316912650057057350374175801344)), (23/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-759196411/9007199254740992), (-349462587/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((300421667/18014398509481984), (-79816623/18014398509481984)), (9/72057594037927936), by norm_num⟩
  | 2 => ⟨((-850483841/576460752303423488), (196328469/144115188075855872)), (5/288230376151711744), by norm_num⟩
  | 3 => ⟨((546626013/9223372036854775808), (-1548636241/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 4 => ⟨((143557019/73786976294838206464), (243094761/18446744073709551616)), (3/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-154560099/295147905179352825856), (-843543741/1180591620717411303424)), (15/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((229358059/4722366482869645213696), (55740003/2361183241434822606848)), (17/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-464895387/151115727451828646838272), (62261963/604462909807314587353088)), (17/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((174553065/1208925819614629174706176), (-99795461/1208925819614629174706176)), (9/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-178333023/38685626227668133590597632), (561956825/77371252455336267181195264)), (33/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((84509197/2475880078570760549798248448), (-132365935/309485009821345068724781056)), (15/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((2537879/309485009821345068724781056), (755126993/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-60284401/79228162514264337593543950336), (-777828943/1267650600228229401496703205376)), (45/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1602248889/288230376151711744), (26605541/18014398509481984)), (3/72057594037927936), by norm_num⟩
  | 1 => ⟨((141747307/144115188075855872), (-65442823/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 2 => ⟨((-546626013/9223372036854775808), (1548636241/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-191409359/73786976294838206464), (-1296505393/73786976294838206464)), (9/36893488147419103232), by norm_num⟩
  | 4 => ⟨((257600165/295147905179352825856), (702953117/590295810358705651712)), (7/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-229358059/2361183241434822606848), (-55740003/1180591620717411303424)), (19/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1084755903/151115727451828646838272), (-36319479/151115727451828646838272)), (23/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-930949681/2417851639229258349412352), (532242459/2417851639229258349412352)), (25/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((534999069/38685626227668133590597632), (-421467619/19342813113834066795298816)), (27/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-140848663/1237940039285380274899124224), (882439567/618970019642690137449562112)), (53/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-297777803/9903520314283042199192993792), (-1384399487/19807040628566084398385987584)), (25/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((60284401/19807040628566084398385987584), (777828943/316912650057057350374175801344)), (47/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-970509323/5070602400912917605986812821504), (-189411685/5070602400912917605986812821504)), (21/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-80998461/288230376151711744), (598334381/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 1 => ⟨((156178861/4611686018427387904), (-884934995/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 2 => ⟨((164065165/73786976294838206464), (1111290337/73786976294838206464)), (9/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-294400189/295147905179352825856), (-803374991/590295810358705651712)), (9/295147905179352825856), by norm_num⟩
  | 4 => ⟨((163827185/1180591620717411303424), (318514303/4722366482869645213696)), (15/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-1859581549/151115727451828646838272), (15565491/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((930949681/1208925819614629174706176), (-133060615/302231454903657293676544)), (29/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-152856877/4835703278458516698824704), (481677279/9671406556917033397649408)), (17/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((90545569/309485009821345068724781056), (-567282579/154742504910672534362390528)), (19/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((425396861/4951760157141521099596496896), (988856777/4951760157141521099596496896)), (5/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-757861041/79228162514264337593543950336), (-38196957/4951760157141521099596496896)), (5/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((415932567/633825300114114700748351602688), (324705747/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-1366963005/40564819207303340847894502572032), (412616111/40564819207303340847894502572032)), (71/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-156178861/18446744073709551616), (442467497/18446744073709551616)), (15/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-164065165/147573952589676412928), (-1111290337/147573952589676412928)), (23/147573952589676412928), by norm_num⟩
  | 2 => ⟨((883200567/1180591620717411303424), (1205062487/1180591620717411303424)), (1/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-1310617481/9444732965739290427392), (-318514303/4722366482869645213696)), (35/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((290559617/18889465931478580854784), (-608027/1180591620717411303424)), (1/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-698212261/604462909807314587353088), (399181845/604462909807314587353088)), (25/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((534999069/9671406556917033397649408), (-842935239/9671406556917033397649408)), (17/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-90545569/154742504910672534362390528), (1134565159/154742504910672534362390528)), (43/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((-478571469/2475880078570760549798248448), (-1112463875/2475880078570760549798248448)), (25/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((473663151/19807040628566084398385987584), (763939141/39614081257132168796771975168)), (7/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-1143814559/633825300114114700748351602688), (-223235201/633825300114114700748351602688)), (59/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((512611127/5070602400912917605986812821504), (-309462083/10141204801825835211973625643008)), (59/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-84460857/20282409603651670423947251286016), (667160191/162259276829213363391578010288128)), (57/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((145835701/590295810358705651712), (3858647/2305843009213693952)), (11/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-785067171/2361183241434822606848), (-1071166655/2361183241434822606848)), (37/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((873744987/9444732965739290427392), (424685737/9444732965739290427392)), (29/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-1033100861/75557863725914323419136), (69179961/151115727451828646838272)), (33/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((775791401/604462909807314587353088), (-55441923/75557863725914323419136)), (33/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-178333023/2417851639229258349412352), (280978413/2417851639229258349412352)), (53/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((70424331/77371252455336267181195264), (-55152473/4835703278458516698824704)), (39/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((212698431/618970019642690137449562112), (494428389/618970019642690137449562112)), (13/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-473663151/9903520314283042199192993792), (-763939141/19807040628566084398385987584)), (1/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((1270905067/316912650057057350374175801344), (31004889/39614081257132168796771975168)), (37/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-626524711/2535301200456458802993406410752), (378231435/5070602400912917605986812821504)), (41/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((900915809/81129638414606681695789005144064), (-889546921/81129638414606681695789005144064)), (43/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((-88730691/324518553658426726783156020576256), (1124030131/1298074214633706907132624082305024)), (87/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((628053735/9444732965739290427392), (214233331/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-349497995/9444732965739290427392), (-679497179/37778931862957161709568)), (59/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((1239721033/151115727451828646838272), (-41507977/151115727451828646838272)), (51/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-620633121/604462909807314587353088), (354828307/604462909807314587353088)), (31/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((178333023/2417851639229258349412352), (-1123913653/9671406556917033397649408)), (1/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-84509197/77371252455336267181195264), (529463741/38685626227668133590597632)), (7/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((-595555607/1237940039285380274899124224), (-1384399489/1237940039285380274899124224)), (85/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((378930521/4951760157141521099596496896), (611151313/9903520314283042199192993792)), (61/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-35744205/4951760157141521099596496896), (-223235201/158456325028528675187087900672)), (39/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((626524711/1267650600228229401496703205376), (-378231435/2535301200456458802993406410752)), (95/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-495503695/20282409603651670423947251286016), (489250807/20282409603651670423947251286016)), (109/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((212953659/324518553658426726783156020576256), (-1348836157/649037107316853453566312041152512)), (15/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((247052893/10384593717069655257060992658440192), (1357312227/10384593717069655257060992658440192)), (63/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3485696/711317811), (-613632/237105937)), 0, by norm_num⟩
  | 1 => ⟨((-17522357043200/168657676081943907), (8555738431488/56219225360647969)), 0, by norm_num⟩
  | 2 => ⟨((12165423/17592186044416), (-1713566013/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((334165211/4503599627370496), (427238203/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-738991341/144115188075855872), (-637900609/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((1012261881/4611686018427387904), (116487529/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-534082963/73786976294838206464), (283792437/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 7 => ⟨((26999487/147573952589676412928), (-797779175/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-416476963/151115727451828646838272), (1179913325/151115727451828646838272)), (21/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-194447601/4835703278458516698824704), (-1317084843/4835703278458516698824704)), (15/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((209351245/38685626227668133590597632), (1142577765/154742504910672534362390528)), (43/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-169453573/618970019642690137449562112), (-658906357/4951760157141521099596496896)), (63/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((1602871637/158456325028528675187087900672), (-13416719/39614081257132168796771975168)), (91/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((634218283/33554432), (611615019/33554432)), (3/16777216), by norm_num⟩
  | 1 => ⟨((719655913/536870912), (134681831/536870912)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((1031758963/137438953472), (-565750593/137438953472)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-462356425/8796093022208), (90566971/1099511627776)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((126217423/1125899906842624), (-939381969/562949953421312)), (25/1125899906842624), by norm_num⟩
  | 5 => ⟨((519755249/36028797018963968), (561438449/18014398509481984)), (39/36028797018963968), by norm_num⟩
  | 6 => ⟨((-726070857/1152921504606846976), (-537225243/1152921504606846976)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((349815789/18446744073709551616), (192979247/73786976294838206464)), (65/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1084075173/2361183241434822606848), (411270407/2361183241434822606848)), (167/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((642363637/75557863725914323419136), (-749084455/75557863725914323419136)), (27/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-359738907/4835703278458516698824704), (844702611/2417851639229258349412352)), (9/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-220223149/77371252455336267181195264), (-1481658795/154742504910672534362390528)), (3/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((124752337/618970019642690137449562112), (497007577/2475880078570760549798248448)), (1013/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-207623219/2251799813685248), (456950937/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((-267332169/9007199254740992), (-683581125/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((591193073/144115188075855872), (63790061/18014398509481984)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-1349682509/4611686018427387904), (-310633411/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 4 => ⟨((534082963/36893488147419103232), (-283792437/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-604788509/1180591620717411303424), (279222711/590295810358705651712)), (7/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((48588979/4722366482869645213696), (-1101252437/37778931862957161709568)), (3/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((116668561/604462909807314587353088), (1580501811/1208925819614629174706176)), (19/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-628053735/19342813113834066795298816), (-856933323/19342813113834066795298816)), (1/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((77666221/38685626227668133590597632), (603997493/618970019642690137449562112)), (25/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-110197425/1237940039285380274899124224), (29516783/9903520314283042199192993792)), (41/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((481460845/158456325028528675187087900672), (-550521493/316912650057057350374175801344)), (1/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-368915183/5070602400912917605986812821504), (18164261/158456325028528675187087900672)), (3/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((79277285/4194304), (305807523/16777216)), (7/33554432), by norm_num⟩
  | 1 => ⟨((719655897/536870912), (269363581/1073741824)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1031759527/137438953472), (-282875053/68719476736)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-462358999/8796093022208), (90566897/1099511627776)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((63116861/562949953421312), (-469692067/281474976710656)), (13/562949953421312), by norm_num⟩
  | 5 => ⟨((64967099/4503599627370496), (280723485/9007199254740992)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-363029497/576460752303423488), (-537258851/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 7 => ⟨((699638699/36893488147419103232), (193075713/73786976294838206464)), (131/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-33879745/73786976294838206464), (411165801/2361183241434822606848)), (21/295147905179352825856), by norm_num⟩
  | 9 => ⟨((642515329/75557863725914323419136), (-749010725/75557863725914323419136)), (217/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-180084683/2417851639229258349412352), (844709817/2417851639229258349412352)), (577/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-439976121/154742504910672534362390528), (-370481901/38685626227668133590597632)), (769/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((997658427/4951760157141521099596496896), (994582787/4951760157141521099596496896)), (507/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-900865635/1152921504606846976), (-777631219/1152921504606846976)), (5/1152921504606846976), by norm_num⟩
  | 1 => ⟨((1542494297/9223372036854775808), (88752403/2305843009213693952)), (9/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-1220761059/73786976294838206464), (162167107/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((8999829/9223372036854775808), (-33240799/36893488147419103232)), (7/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-277651309/9444732965739290427392), (196652221/2361183241434822606848)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-233337121/302231454903657293676544), (-1580501811/302231454903657293676544)), (19/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((837404981/4835703278458516698824704), (1142577765/4835703278458516698824704)), (19/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-1065136745/77371252455336267181195264), (-517712137/77371252455336267181195264)), (19/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((1889098715/2475880078570760549798248448), (-7906281/309485009821345068724781056)), (35/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-1260968879/39614081257132168796771975168), (720921003/39614081257132168796771975168)), (1/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((579723859/633825300114114700748351602688), (-913402839/633825300114114700748351602688)), (27/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-124873619/20282409603651670423947251286016), (195588337/2535301200456458802993406410752)), (23/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-220003225/162259276829213363391578010288128), (-1022817515/324518553658426726783156020576256)), (19/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((79277285/4194304), (305807523/16777216)), (1/4194304), by norm_num⟩
  | 1 => ⟨((719655897/536870912), (269363581/1073741824)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((1031759525/137438953472), (-565750105/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-231179495/4398046511104), (5660431/68719476736)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((126233689/1125899906842624), (-939384087/562949953421312)), (27/1125899906842624), by norm_num⟩
  | 5 => ⟨((129934191/9007199254740992), (140361719/4503599627370496)), (41/36028797018963968), by norm_num⟩
  | 6 => ⟨((-363029397/576460752303423488), (-537258579/1152921504606846976)), (27/576460752303423488), by norm_num⟩
  | 7 => ⟨((699638191/36893488147419103232), (193075219/73786976294838206464)), (33/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-542075019/1180591620717411303424), (411165741/2361183241434822606848)), (169/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((160628231/18889465931478580854784), (-374504675/37778931862957161709568)), (109/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-360164943/4835703278458516698824704), (1689412665/4835703278458516698824704)), (289/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-219988537/77371252455336267181195264), (-740957833/77371252455336267181195264)), (385/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((997651713/4951760157141521099596496896), (248641795/1237940039285380274899124224)), (1015/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((976608847/295147905179352825856), (-259467371/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-172796717/295147905179352825856), (159555835/295147905179352825856)), (11/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((166590785/4722366482869645213696), (-943930661/9444732965739290427392)), (3/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((233337123/151115727451828646838272), (395125453/37778931862957161709568)), (23/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-78506717/151115727451828646838272), (-214233331/302231454903657293676544)), (9/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((1118393583/19342813113834066795298816), (33974859/1208925819614629174706176)), (3/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((-1322369101/309485009821345068724781056), (22137587/154742504910672534362390528)), (29/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((141858999/618970019642690137449562112), (-324414451/2475880078570760549798248448)), (31/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-652189341/79228162514264337593543950336), (1027578195/79228162514264337593543950336)), (17/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((42925307/633825300114114700748351602688), (-1075735853/1267650600228229401496703205376)), (33/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((181502661/10141204801825835211973625643008), (843824449/20282409603651670423947251286016)), (31/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-146979111/81129638414606681695789005144064), (-948210521/649037107316853453566312041152512)), (29/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((1183097079/10384593717069655257060992658440192), (28862733/1298074214633706907132624082305024)), (53/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((79277285/4194304), (305807523/16777216)), (9/33554432), by norm_num⟩
  | 1 => ⟨((719655897/536870912), (269363581/1073741824)), (1/134217728), by norm_num⟩
  | 2 => ⟨((1031759525/137438953472), (-565750105/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-231179495/4398046511104), (5660431/68719476736)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((15779211/140737488355328), (-1878768175/1125899906842624)), (7/281474976710656), by norm_num⟩
  | 5 => ⟨((259868383/18014398509481984), (1122893753/36028797018963968)), (21/18014398509481984), by norm_num⟩
  | 6 => ⟨((-726058799/1152921504606846976), (-537258579/1152921504606846976)), (55/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1399276399/73786976294838206464), (193075209/73786976294838206464)), (133/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1084150057/2361183241434822606848), (102791443/590295810358705651712)), (85/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((642512929/75557863725914323419136), (-374504707/37778931862957161709568)), (219/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-45020607/604462909807314587353088), (844706433/2417851639229258349412352)), (579/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-219988677/77371252455336267181195264), (-370478973/38685626227668133590597632)), (771/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((997652277/4951760157141521099596496896), (497283645/2475880078570760549798248448)), (127/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-538475265/75557863725914323419136), (1525544501/75557863725914323419136)), (27/75557863725914323419136), by norm_num⟩
  | 1 => ⟨((-141416439/151115727451828646838272), (-478939943/75557863725914323419136)), (21/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((95159657/151115727451828646838272), (259676765/302231454903657293676544)), (29/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((-1129690489/9671406556917033397649408), (-274544315/4835703278458516698824704)), (31/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((500897387/38685626227668133590597632), (-33541799/77371252455336267181195264)), (57/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-1203652113/1237940039285380274899124224), (688151867/1237940039285380274899124224)), (11/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((461143979/9903520314283042199192993792), (-363285221/4951760157141521099596496896)), (15/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((-156092025/316912650057057350374175801344), (488970843/79228162514264337593543950336)), (75/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((-412506047/2535301200456458802993406410752), (-958891421/2535301200456458802993406410752)), (11/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((816550617/40564819207303340847894502572032), (658479529/40564819207303340847894502572032)), (49/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-985914233/649037107316853453566312041152512), (-48104555/162259276829213363391578010288128)), (13/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((110461657/1298074214633706907132624082305024), (-8335679/324518553658426726783156020576256)), (51/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((-582410219/166153499473114484112975882535043072), (143765159/41538374868278621028243970633760768)), (25/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((79277285/4194304), (305807523/16777216)), (5/16777216), by norm_num⟩
  | 1 => ⟨((719655897/536870912), (269363581/1073741824)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((1031759525/137438953472), (-565750105/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-231179495/4398046511104), (5660431/68719476736)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((15779211/140737488355328), (-1878768175/1125899906842624)), (29/1125899906842624), by norm_num⟩
  | 5 => ⟨((259868383/18014398509481984), (1122893753/36028797018963968)), (43/36028797018963968), by norm_num⟩
  | 6 => ⟨((-726058799/1152921504606846976), (-537258579/1152921504606846976)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((1399276399/73786976294838206464), (193075209/73786976294838206464)), (67/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1084150057/2361183241434822606848), (411165771/2361183241434822606848)), (171/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((642512931/75557863725914323419136), (-749009413/75557863725914323419136)), (55/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-360164863/4835703278458516698824704), (1689412865/4835703278458516698824704)), (145/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-439977341/154742504910672534362390528), (-185239487/19342813113834066795298816)), (193/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((249413065/1237940039285380274899124224), (994567307/4951760157141521099596496896)), (1017/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-616606691/4835703278458516698824704), (-420657335/2417851639229258349412352)), (33/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((1372511873/19342813113834066795298816), (667112515/19342813113834066795298816)), (59/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((-1217125607/77371252455336267181195264), (10187861/19342813113834066795298816)), (51/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((1218642653/618970019642690137449562112), (-348361129/309485009821345068724781056)), (31/309485009821345068724781056), by norm_num⟩
  | 4 => ⟨((-350165373/2475880078570760549798248448), (1103428957/4951760157141521099596496896)), (1/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((41484457/19807040628566084398385987584), (-1039627239/39614081257132168796771975168)), (7/4951760157141521099596496896), by norm_num⟩
  | 6 => ⟨((584700881/633825300114114700748351602688), (679583561/316912650057057350374175801344)), (85/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-744048101/5070602400912917605986812821504), (-37500771/316912650057057350374175801344)), (61/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((561483573/40564819207303340847894502572032), (54791617/20282409603651670423947251286016)), (39/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((-615105535/649037107316853453566312041152512), (185668853/649037107316853453566312041152512)), (47/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((972945073/20769187434139310514121985316880384), (-480333615/10384593717069655257060992658440192)), (27/5192296858534827628530496329220096), by norm_num⟩
  | 11 => ⟨((-209072319/166153499473114484112975882535043072), (1324251975/332306998946228968225951765070086144)), (119/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((-242550053/5316911983139663491615228241121378304), (-666286779/2658455991569831745807614120560689152)), (31/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((79277285/4194304), (305807523/16777216)), (11/33554432), by norm_num⟩
  | 1 => ⟨((719655897/536870912), (269363581/1073741824)), (5/536870912), by norm_num⟩
  | 2 => ⟨((1031759525/137438953472), (-565750105/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-231179495/4398046511104), (5660431/68719476736)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((15779211/140737488355328), (-1878768175/1125899906842624)), (15/562949953421312), by norm_num⟩
  | 5 => ⟨((259868383/18014398509481984), (1122893753/36028797018963968)), (11/9007199254740992), by norm_num⟩
  | 6 => ⟨((-726058799/1152921504606846976), (-537258579/1152921504606846976)), (57/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1399276399/73786976294838206464), (193075209/73786976294838206464)), (135/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1084150057/2361183241434822606848), (411165771/2361183241434822606848)), (43/590295810358705651712), by norm_num⟩
  | 9 => ⟨((642512931/75557863725914323419136), (-749009413/75557863725914323419136)), (221/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-360164863/4835703278458516698824704), (1689412865/4835703278458516698824704)), (581/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-439977341/154742504910672534362390528), (-1481915895/154742504910672534362390528)), (773/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((249413065/1237940039285380274899124224), (497283653/2475880078570760549798248448)), (509/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1102308041070035/8388608), (-24696642431393/262144)), (370533053/4194304), by norm_num⟩
  | 1 => ⟨((799112331/4), (-186640871/2)), 143, by norm_num⟩
  | 2 => ⟨(146201668, (-309886979/8)), (465/4), by norm_num⟩
  | 3 => ⟨((1108955833/16), (-48655331/8)), (1015/16), by norm_num⟩
  | 4 => ⟨((770400675/32), (120203149/64)), (209/8), by norm_num⟩
  | 5 => ⟨((839093261/128), (406330375/256)), (555/64), by norm_num⟩
  | 6 => ⟨((373608649/256), (617686123/1024)), (1239/512), by norm_num⟩
  | 7 => ⟨((139863545/512), (168193847/1024)), (2391/4096), by norm_num⟩
  | 8 => ⟨((358862089/8192), (587702211/16384)), (2035/16384), by norm_num⟩
  | 9 => ⟨((798249433/131072), (433381459/65536)), (97/4096), by norm_num⟩
  | 10 => ⟨((386866445/524288), (555914787/524288)), (537/131072), by norm_num⟩
  | 11 => ⟨((325797245/4194304), (1265344187/8388608)), (681/1048576), by norm_num⟩
  | 12 => ⟨((468336809/67108864), (1296106505/67108864)), (3193/33554432), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((804298330657545/5070602400912917605986812821504), (-810233751843/10141204801825835211973625643008)), (427031/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((905832007318581/316912650057057350374175801344), (-992063463277/633825300114114700748351602688)), (261691/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1926785454335593/39614081257132168796771975168), (-1118768678171/39614081257132168796771975168)), (590287/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1928910309775933/2475880078570760549798248448), (-595517754923/1237940039285380274899124224)), (628459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1810615359713531/154742504910672534362390528), (-596830061313/77371252455336267181195264)), (629889/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((793277680055833/4835703278458516698824704), (-560926401301/4835703278458516698824704)), (296023/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((645603386323169/302231454903657293676544), (-984426861945/604462909807314587353088)), (519571/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((485137313222439/18889465931478580854784), (-802486975873/37778931862957161709568)), (847183/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((83573477601411/295147905179352825856), (-604185251637/2361183241434822606848)), (318959/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((104753700068409/36893488147419103232), (-1669086770941/590295810358705651712)), (110159/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1891906115779155/73786976294838206464), (-262223755259/9223372036854775808)), (276957/18446744073709551616), by norm_num⟩
  | 7 => ⟨((237484234741443/1152921504606846976), (-1187919747127/4611686018427387904)), (1254945/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1671413414150581/1152921504606846976), (-2395783765867/1152921504606846976)), (632917/576460752303423488), by norm_num⟩
  | 5 => ⟨((78916218357871/9007199254740992), (-2118973081777/144115188075855872)), (559991/72057594037927936), by norm_num⟩
  | 4 => ⟨((199302539834769/4503599627370496), (-3224352779397/36028797018963968)), (1705049/36028797018963968), by norm_num⟩
  | 3 => ⟨((809456219366255/4503599627370496), (-2056025180865/4503599627370496)), (1087963/4503599627370496), by norm_num⟩
  | 2 => ⟨((622709316450699/1125899906842624), (-2118550187371/1125899906842624)), (2244337/2251799813685248), by norm_num⟩
  | 1 => ⟨((654892310123753/562949953421312), (-6677699009151/1125899906842624)), (1771429/562949953421312), by norm_num⟩
  | 0 => ⟨((756327439414649/562949953421312), (-14701746335099/1125899906842624)), (3912015/562949953421312), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((756327439414649/562949953421312), (-14701746335099/1125899906842624)), (14923152925731468023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2032071081271149/1125899906842624), (-39503810571337/1125899906842624)), (21227615/1125899906842624), by norm_num⟩
  | 2 => ⟨((1833090269926547/562949953421312), (-71298123904409/562949953421312)), (39057287/562949953421312), by norm_num⟩
  | 3 => ⟨((372494980996573/35184372088832), (-116081275430337/140737488355328)), (66062929/140737488355328), by norm_num⟩
  | 4 => ⟨((244977961402955/2199023255552), (-153618246960297/8796093022208)), (94236717/8796093022208), by norm_num⟩
  | 5 => ⟨((831893362526167/68719476736), (-133699575764827/34359738368)), (379501441/137438953472), by norm_num⟩
  | 6 => ⟨((1102308041070035/8388608), (-24696642431393/262144)), (370533053/4194304), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((79277285/4194304), (305807523/16777216)), (11/33554432), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((1359872/53474065), (-7363584/53474065)), 0, by norm_num⟩
  | 1 => ⟨((26186558734336/2859475627624225), (10013531701248/2859475627624225)), 0, by norm_num⟩
  | 2 => ⟨((-98283937/274877906944), (644320569/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-629822227/17592186044416), (-564173545/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((374822217/140737488355328), (-72381725/35184372088832)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((60674101/562949953421312), (471818165/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-284572249/18014398509481984), (171373251/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((-18250255/144115188075855872), (-1323703819/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((185992001/2305843009213693952), (27114807/4611686018427387904)), (17/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-211096811/147573952589676412928), (404272655/73786976294838206464)), (23/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-13246437/36893488147419103232), (-99261099/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 11 => ⟨((76233799/4722366482869645213696), (-53322209/2361183241434822606848)), (11/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((815787671/604462909807314587353088), (211355315/151115727451828646838272)), (15/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((83/64), (7191/1024)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((83/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((83/64), (7191/1024)))⁻¹=value ((1359872/53474065), (-7363584/53474065)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((1359872/53474065), (-7363584/53474065))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((147/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((802816/19080795), (-818176/6360265)), 0, by norm_num⟩
  | 1 => ⟨((2690097086464/364076737832025), (656844783616/121358912610675)), 0, by norm_num⟩
  | 2 => ⟨((-1107347967/2199023255552), (794686151/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-445089523/35184372088832), (-703535329/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((1597845087/562949953421312), (7784611/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-138462857/2251799813685248), (204889591/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-375101469/36028797018963968), (-140211819/18014398509481984)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((829688811/1152921504606846976), (-291630815/576460752303423488)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((160484833/9223372036854775808), (16408817/288230376151711744)), (1/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-1188771111/295147905179352825856), (-362011/4611686018427387904)), (23/295147905179352825856), by norm_num⟩
  | 10 => ⟨((211989637/2361183241434822606848), (-37986779/147573952589676412928)), (1/147573952589676412928), by norm_num⟩
  | 11 => ⟨((554125813/37778931862957161709568), (845479911/75557863725914323419136)), (45/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-1243124829/1208925819614629174706176), (106990817/151115727451828646838272)), (31/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((147/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((147/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((147/64), (7191/1024)))⁻¹=value ((802816/19080795), (-818176/6360265)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((802816/19080795), (-818176/6360265))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-679295844352/40813106883267), (-616629796864/68021844805445)), 0, by norm_num⟩
  | 1 => ⟨((486258897/274877906944), (-262582337/137438953472)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((642152941/4398046511104), (987909975/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-814554931/35184372088832), (278723567/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-49278109/281474976710656), (-1173676821/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((1524637041/9007199254740992), (248155933/9007199254740992)), (9/9007199254740992), by norm_num⟩
  | 6 => ⟨((-194043029/36028797018963968), (56474611/4503599627370496)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((-975690849/1152921504606846976), (-740442189/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((1166966341/18446744073709551616), (-470852529/9223372036854775808)), (19/18446744073709551616), by norm_num⟩
  | 9 => ⟨((383288743/147573952589676412928), (820129661/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-1059761603/2361183241434822606848), (210744067/2361183241434822606848)), (23/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((13936145/9444732965739290427392), (-637947649/18889465931478580854784)), (33/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((359337521/151115727451828646838272), (52182249/75557863725914323419136)), (23/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((211/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((3457024/63107857), (-7363584/63107857)), 0, by norm_num⟩
  | 1 => ⟨((21135677194240/3982601615132449), (25456086614016/3982601615132449)), 0, by norm_num⟩
  | 2 => ⟨((-1139676399/2199023255552), (18491919/137438953472)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((6977023/1099511627776), (-1193504007/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((508122813/281474976710656), (365723123/281474976710656)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((-1128132289/9007199254740992), (157019523/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-91896689/144115188075855872), (-1328313577/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((1280200361/2305843009213693952), (124083533/576460752303423488)), (17/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-1024339197/36893488147419103232), (488752067/18446744073709551616)), (3/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-463557951/590295810358705651712), (-692279123/295147905179352825856)), (17/295147905179352825856), by norm_num⟩
  | 10 => ⟨((747789101/4722366482869645213696), (87025815/4722366482869645213696)), (3/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-817887831/151115727451828646838272), (329946715/37778931862957161709568)), (67/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-54596241/151115727451828646838272), (-670922519/1208925819614629174706176)), (47/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((211/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((211/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((211/64), (7191/1024)))⁻¹=value ((3457024/63107857), (-7363584/63107857)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((3457024/63107857), (-7363584/63107857))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-541372725/274877906944), (794663437/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((-85986409/549755813888), (-1023787517/2199023255552)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((1154992153/17592186044416), (-19441839/17592186044416)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-292401343/140737488355328), (492290219/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-680155679/1125899906842624), (-457799797/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((237589045/4503599627370496), (-762882703/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((316168535/144115188075855872), (800284263/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((-1165279479/2305843009213693952), (22746627/576460752303423488)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((83456769/9223372036854775808), (-1503117279/36893488147419103232)), (23/36893488147419103232), by norm_num⟩
  | 9 => ⟨((861784811/295147905179352825856), (485574451/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-448928345/2361183241434822606848), (431022719/2361183241434822606848)), (15/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-702853191/75557863725914323419136), (-684344269/37778931862957161709568)), (23/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((920263767/604462909807314587353088), (-43245817/151115727451828646838272)), (17/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((275/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((4505600/71070481), (-7363584/71070481)), 0, by norm_num⟩
  | 1 => ⟨((16960968982528/5051013269571361), (33177364070400/5051013269571361)), 0, by norm_num⟩
  | 2 => ⟨((-245585689/549755813888), (-75317841/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((560643767/35184372088832), (-12125659/549755813888)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((89725443/140737488355328), (429144871/281474976710656)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-13960009/140737488355328), (-137813269/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((567356277/144115188075855872), (-335328715/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((67036605/576460752303423488), (202601407/576460752303423488)), (5/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-403861087/18446744073709551616), (-377505797/73786976294838206464)), (7/18446744073709551616), by norm_num⟩
  | 9 => ⟨((566105171/590295810358705651712), (-143443099/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 10 => ⟨((188475187/9444732965739290427392), (380115727/4722366482869645213696)), (55/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-181431781/37778931862957161709568), (-458687419/302231454903657293676544)), (37/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((558164541/2417851639229258349412352), (-970444339/4835703278458516698824704)), (25/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((275/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((275/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((275/64), (7191/1024)))⁻¹=value ((4505600/71070481), (-7363584/71070481)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((4505600/71070481), (-7363584/71070481))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109542309/4398046511104), (1300491849/4398046511104)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-653204277/8796093022208), (-94084701/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((264229235/35184372088832), (-22081227/2199023255552)), (3/70368744177664), by norm_num⟩
  | 3 => ⟨((492732155/562949953421312), (769053439/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((-1611763431/9007199254740992), (349956619/9007199254740992)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((188511475/72057594037927936), (-336009993/18014398509481984)), (13/72057594037927936), by norm_num⟩
  | 6 => ⟨((921062193/576460752303423488), (490862235/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 7 => ⟨((-141473523/1152921504606846976), (510252971/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-405080467/73786976294838206464), (-987600655/73786976294838206464)), (19/73786976294838206464), by norm_num⟩
  | 9 => ⟨((721910065/590295810358705651712), (-34451481/590295810358705651712)), (1/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-272784015/9444732965739290427392), (227800309/2361183241434822606848)), (27/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-123707595/18889465931478580854784), (-716132757/151115727451828646838272)), (21/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1257185923/2417851639229258349412352), (-441182261/1208925819614629174706176)), (33/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((339/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((1851392/27043419), (-818176/9014473)), 0, by norm_num⟩
  | 1 => ⟨((1298527682560/731346511209561), (1514764500992/243782170403187)), 0, by norm_num⟩
  | 2 => ⟨((-1507462119/4398046511104), (-290525405/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1247507585/70368744177664), (-194084569/17592186044416)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-119535633/1125899906842624), (1330999981/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((-450485851/9007199254740992), (-815756699/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((1085764921/288230376151711744), (-405121/562949953421312)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((-444042523/4611686018427387904), (901974633/4611686018427387904)), (1/288230376151711744), by norm_num⟩
  | 8 => ⟨((-102932637/18446744073709551616), (-816412577/73786976294838206464)), (11/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1636587251/2361183241434822606848), (296350431/2361183241434822606848)), (57/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-1111505901/37778931862957161709568), (513010343/18889465931478580854784)), (73/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-136244125/604462909807314587353088), (-1368995199/604462909807314587353088)), (47/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1068645449/9671406556917033397649408), (20338883/302231454903657293676544)), (121/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((339/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((339/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((339/64), (7191/1024)))⁻¹=value ((1851392/27043419), (-818176/9014473)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((1851392/27043419), (-818176/9014473))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((502140563/17592186044416), (632714537/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-155139107/17592186044416), (838140799/140737488355328)), (7/140737488355328), by norm_num⟩
  | 2 => ⟨((-51461489/140737488355328), (-1110755025/562949953421312)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((1287897511/4503599627370496), (292859025/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 4 => ⟨((-386656837/18014398509481984), (534178685/18014398509481984)), (13/36028797018963968), by norm_num⟩
  | 5 => ⟨((-612434609/288230376151711744), (-504900649/144115188075855872)), (15/288230376151711744), by norm_num⟩
  | 6 => ⟨((241187121/576460752303423488), (-18224293/288230376151711744)), (15/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-180973111/18446744073709551616), (735351667/18446744073709551616)), (29/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-904299027/295147905179352825856), (-328760955/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 9 => ⟨((167881669/590295810358705651712), (-419773571/2361183241434822606848)), (11/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((193128323/37778931862957161709568), (33314203/1180591620717411303424)), (19/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-1410835161/604462909807314587353088), (-280435575/604462909807314587353088)), (31/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((125029445/1208925819614629174706176), (-392216573/2417851639229258349412352)), (49/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((403/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((6602752/93287185), (-7363584/93287185)), 0, by norm_num⟩
  | 1 => ⟨((5313017675776/8702498885224225), (48619918983168/8702498885224225)), 0, by norm_num⟩
  | 2 => ⟨((-266197537/1099511627776), (-763594259/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1085108163/70368744177664), (-240019949/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-231426987/562949953421312), (821126915/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-64110135/4503599627370496), (-1514456503/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((1246752531/576460752303423488), (533658533/576460752303423488)), (5/288230376151711744), by norm_num⟩
  | 7 => ⟨((-1042941725/9223372036854775808), (242560735/4611686018427387904)), (13/9223372036854775808), by norm_num⟩
  | 8 => ⟨((284202197/147573952589676412928), (-466641833/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 9 => ⟨((214211461/1180591620717411303424), (176980093/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-689621103/37778931862957161709568), (-260613627/75557863725914323419136)), (49/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472769955/604462909807314587353088), (-180847963/302231454903657293676544)), (15/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-78588189/19342813113834066795298816), (503346287/9671406556917033397649408)), (73/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((403/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((403/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((403/64), (7191/1024)))⁻¹=value ((6602752/93287185), (-7363584/93287185)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((6602752/93287185), (-7363584/93287185))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((968198653/281474976710656), (-275917963/281474976710656)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((-266986111/1125899906842624), (1450221237/1125899906842624)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((-252280813/1125899906842624), (-746394689/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 3 => ⟨((717771693/18014398509481984), (-377377381/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((68650149/288230376151711744), (1760204073/288230376151711744)), (11/144115188075855872), by norm_num⟩
  | 5 => ⟨((-779822255/1152921504606846976), (-165426661/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 6 => ⟨((1104688947/18446744073709551616), (-996869583/18446744073709551616)), (15/9223372036854775808), by norm_num⟩
  | 7 => ⟨((181940363/73786976294838206464), (1161679957/147573952589676412928)), (29/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-466716241/590295810358705651712), (-229261125/2361183241434822606848)), (55/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((358042795/9444732965739290427392), (-74142205/1180591620717411303424)), (49/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((281544831/75557863725914323419136), (100348267/18889465931478580854784)), (43/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-1313751923/2417851639229258349412352), (133537681/1208925819614629174706176)), (9/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((363064709/38685626227668133590597632), (-870406019/19342813113834066795298816)), (117/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((467/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((7651328/107541265), (-7363584/107541265)), 0, by norm_num⟩
  | 1 => ⟨((-2160225419264/11565123677800225), (56341196439552/11565123677800225)), 0, by norm_num⟩
  | 2 => ⟨((-704309049/4398046511104), (-197580525/1099511627776)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((833801069/70368744177664), (128066155/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-509660987/1125899906842624), (105072711/281474976710656)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((935381/281474976710656), (-1036806043/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((499791355/576460752303423488), (655716739/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 7 => ⟨((-643659371/9223372036854775808), (-99448205/9223372036854775808)), (21/18446744073709551616), by norm_num⟩
  | 8 => ⟨((210417617/73786976294838206464), (-295977847/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-309608609/9444732965739290427392), (1595957923/9444732965739290427392)), (55/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-349002895/75557863725914323419136), (-538994089/75557863725914323419136)), (31/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((987790333/2417851639229258349412352), (115610203/1208925819614629174706176)), (35/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-688890443/38685626227668133590597632), (204741275/19342813113834066795298816)), (79/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((467/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((467/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((467/64), (7191/1024)))⁻¹=value ((7651328/107541265), (-7363584/107541265)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((7651328/107541265), (-7363584/107541265))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((399940273/2251799813685248), (-42962815/140737488355328)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((339830491/4503599627370496), (1124274059/9007199254740992)), (13/9007199254740992), by norm_num⟩
  | 2 => ⟨((-616954687/18014398509481984), (61036369/36028797018963968)), (7/18014398509481984), by norm_num⟩
  | 3 => ⟨((184522893/72057594037927936), (-98204735/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((305893659/576460752303423488), (806799523/1152921504606846976)), (17/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-1020177907/9223372036854775808), (176806487/9223372036854775808)), (11/4611686018427387904), by norm_num⟩
  | 6 => ⟨((70815523/18446744073709551616), (-915995033/73786976294838206464)), (25/73786976294838206464), by norm_num⟩
  | 7 => ⟨((295997521/295147905179352825856), (142301941/147573952589676412928)), (25/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-621419035/4722366482869645213696), (446365765/9444732965739290427392)), (49/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((55165391/37778931862957161709568), (-250290631/18889465931478580854784)), (23/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((622932385/604462909807314587353088), (778765237/1208925819614629174706176)), (41/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-868590797/9671406556917033397649408), (555427555/9671406556917033397649408)), (35/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-183327479/154742504910672534362390528), (-346698365/38685626227668133590597632)), (29/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((531/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((966656/13765833), (-818176/13765833)), 0, by norm_num⟩
  | 1 => ⟨((-44168642560/63166052727963), (790894739456/189498158183889)), 0, by norm_num⟩
  | 2 => ⟨((-218757311/2199023255552), (-735876431/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((148919803/17592186044416), (410727521/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-864564415/2251799813685248), (335734799/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((326051449/36028797018963968), (-599691083/36028797018963968)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((203952219/1152921504606846976), (983841607/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-582373607/18446744073709551616), (-911436403/36893488147419103232)), (11/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1087693145/590295810358705651712), (-41797833/590295810358705651712)), (3/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-295580259/4722366482869645213696), (540659503/9444732965739290427392)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((75022983/151115727451828646838272), (-584813197/151115727451828646838272)), (55/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471844987/4835703278458516698824704), (364203279/2417851639229258349412352)), (29/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-1222826459/154742504910672534362390528), (-184843925/77371252455336267181195264)), (61/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((531/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((531/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((531/64), (7191/1024)))⁻¹=value ((966656/13765833), (-818176/13765833)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((966656/13765833), (-818176/13765833))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-102173921/18014398509481984), (-1152657585/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 1 => ⟨((499622151/36028797018963968), (94303457/18014398509481984)), (15/72057594037927936), by norm_num⟩
  | 2 => ⟨((-212332317/72057594037927936), (686794113/288230376151711744)), (9/144115188075855872), by norm_num⟩
  | 3 => ⟨((-64297465/576460752303423488), (-407119451/576460752303423488)), (31/2305843009213693952), by norm_num⟩
  | 4 => ⟨((957001749/9223372036854775808), (90119605/2305843009213693952)), (23/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-843546719/73786976294838206464), (355333309/36893488147419103232)), (31/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-208425361/590295810358705651712), (-1049427379/590295810358705651712)), (37/590295810358705651712), by norm_num⟩
  | 7 => ⟨((227812389/1180591620717411303424), (283499175/4722366482869645213696)), (39/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-566332075/37778931862957161709568), (557861995/37778931862957161709568)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-361158665/604462909807314587353088), (-299389033/151115727451828646838272)), (75/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((921242487/4835703278458516698824704), (173064689/4835703278458516698824704)), (69/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-823670003/77371252455336267181195264), (532917113/38685626227668133590597632)), (15/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-100806843/154742504910672534362390528), (-841143475/618970019642690137449562112)), (51/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((595/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((573440/8372993), (-433152/8372993)), 0, by norm_num⟩
  | 1 => ⟨((-70606389248/70107011778049), (248386682880/70107011778049)), 0, by norm_num⟩
  | 2 => ⟨((-62842643/1099511627776), (-1296311333/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((405967963/70368744177664), (502179747/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-652685795/2251799813685248), (60883095/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((664812705/72057594037927936), (-37934459/4503599627370496)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-113056833/1152921504606846976), (151920617/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 7 => ⟨((-189549965/18446744073709551616), (-379735397/18446744073709551616)), (13/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1044037385/1180591620717411303424), (259217261/590295810358705651712)), (13/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-1573160275/37778931862957161709568), (148033841/18889465931478580854784)), (51/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((369698491/302231454903657293676544), (-203319069/151115727451828646838272)), (25/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-137064603/19342813113834066795298816), (23487313/302231454903657293676544)), (97/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-136751715/77371252455336267181195264), (-440157039/154742504910672534362390528)), (47/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((595/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((595/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((595/64), (7191/1024)))⁻¹=value ((573440/8372993), (-433152/8372993)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((573440/8372993), (-433152/8372993))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-588995753/288230376151711744), (-273482273/144115188075855872)), (9/144115188075855872), by norm_num⟩
  | 1 => ⟨((386113611/288230376151711744), (-199880103/576460752303423488)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((-16637719/144115188075855872), (835067355/2305843009213693952)), (21/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-228685501/4611686018427387904), (-534822285/9223372036854775808)), (37/18446744073709551616), by norm_num⟩
  | 4 => ⟨((1818976065/147573952589676412928), (-146686675/73786976294838206464)), (57/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-386859379/590295810358705651712), (120857607/73786976294838206464)), (39/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-321299465/2361183241434822606848), (-208409723/1180591620717411303424)), (49/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((241284645/9444732965739290427392), (-31599301/9444732965739290427392)), (27/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-19853615/18889465931478580854784), (193592593/75557863725914323419136)), (7/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-839928109/4835703278458516698824704), (-1062405345/4835703278458516698824704)), (109/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((1026305691/38685626227668133590597632), (-84601155/19342813113834066795298816)), (51/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-251232273/309485009821345068724781056), (1442294313/618970019642690137449562112)), (91/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-729841175/4951760157141521099596496896), (-198266727/1237940039285380274899124224)), (157/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((659/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((10797056/162886417), (-7363584/162886417)), 0, by norm_num⟩
  | 1 => ⟨((-31177024471040/26531984843097889), (79505028808704/26531984843097889)), 0, by norm_num⟩
  | 2 => ⟨((-63304383/2199023255552), (-1107215257/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1069415277/281474976710656), (991127609/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-1851085033/9007199254740992), (-277644373/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((541008313/72057594037927936), (-522222957/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-192457091/1152921504606846976), (1336488685/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-75118197/73786976294838206464), (-1974267897/147573952589676412928)), (23/147573952589676412928), by norm_num⟩
  | 8 => ⟨((396835993/1180591620717411303424), (496296821/1180591620717411303424)), (21/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-1559699607/75557863725914323419136), (-478647037/75557863725914323419136)), (39/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((125024063/151115727451828646838272), (-310253013/1208925819614629174706176)), (35/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-418183935/19342813113834066795298816), (1052494947/38685626227668133590597632)), (63/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((125749051/1237940039285380274899124224), (-860600277/618970019642690137449562112)), (113/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((659/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((659/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((659/64), (7191/1024)))⁻¹=value ((10797056/162886417), (-7363584/162886417)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((10797056/162886417), (-7363584/162886417))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-127537209/576460752303423488), (-154069287/4611686018427387904)), (33/4611686018427387904), by norm_num⟩
  | 1 => ⟨((374512073/4611686018427387904), (-201614693/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((36912481/4611686018427387904), (626416441/18446744073709551616)), (43/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-1024339093/147573952589676412928), (-375787903/147573952589676412928)), (41/147573952589676412928), by norm_num⟩
  | 4 => ⟨((1198027619/1180591620717411303424), (-449502269/590295810358705651712)), (1/18446744073709551616), by norm_num⟩
  | 5 => ⟨((133963267/9444732965739290427392), (220030835/1180591620717411303424)), (45/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-819161241/37778931862957161709568), (-430914883/37778931862957161709568)), (29/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((761203937/302231454903657293676544), (-224973257/151115727451828646838272)), (33/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-8860137/2417851639229258349412352), (782467399/2417851639229258349412352)), (141/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-1107911305/38685626227668133590597632), (-338875537/19342813113834066795298816)), (35/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((449677109/154742504910672534362390528), (-120383467/77371252455336267181195264)), (135/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-11900873/1237940039285380274899124224), (95447157/309485009821345068724781056)), (245/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-937371091/39614081257132168796771975168), (-570124571/39614081257132168796771975168)), (27/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((723/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((3948544/61843035), (-818176/20614345)), 0, by norm_num⟩
  | 1 => ⟨((-4783146008576/3824560978011225), (3230603935744/1274853659337075)), 0, by norm_num⟩
  | 2 => ⟨((-45578783/4398046511104), (-1859793939/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((683639879/281474976710656), (892062377/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1264873039/9007199254740992), (-14911415/281474976710656)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((99697927/18014398509481984), (-157891111/144115188075855872)), (9/288230376151711744), by norm_num⟩
  | 6 => ⟨((-714517341/4611686018427387904), (667788915/4611686018427387904)), (9/4611686018427387904), by norm_num⟩
  | 7 => ⟨((305857323/147573952589676412928), (-8874477/1152921504606846976)), (1/9223372036854775808), by norm_num⟩
  | 8 => ⟨((204451595/2361183241434822606848), (1354659781/4722366482869645213696)), (27/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-638988381/75557863725914323419136), (-281051499/37778931862957161709568)), (23/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1009723093/2417851639229258349412352), (21055679/302231454903657293676544)), (39/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-284616697/19342813113834066795298816), (469130767/77371252455336267181195264)), (33/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((216276035/618970019642690137449562112), (-1202213205/2475880078570760549798248448)), (55/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((723/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((723/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((723/64), (7191/1024)))⁻¹=value ((3948544/61843035), (-818176/20614345)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((3948544/61843035), (-818176/20614345))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1140140067/73786976294838206464), (7664565/1152921504606846976)), (7/9223372036854775808), by norm_num⟩
  | 1 => ⟨((76593649/36893488147419103232), (-344019389/36893488147419103232)), (29/73786976294838206464), by norm_num⟩
  | 2 => ⟨((291842323/147573952589676412928), (646182063/295147905179352825856)), (41/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-768361259/1180591620717411303424), (194234171/2361183241434822606848)), (81/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((253648533/4722366482869645213696), (-986377071/9444732965739290427392)), (33/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((654371157/75557863725914323419136), (1189017833/75557863725914323419136)), (47/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-366590001/151115727451828646838272), (-119790085/604462909807314587353088)), (31/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((55337593/302231454903657293676544), (-286311065/1208925819614629174706176)), (73/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((27720993/2417851639229258349412352), (1238018653/38685626227668133590597632)), (159/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-1090920811/309485009821345068724781056), (-120083405/154742504910672534362390528)), (163/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((623219585/2475880078570760549798248448), (-321688029/1237940039285380274899124224)), (5/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((173267927/19807040628566084398385987584), (82604205/2475880078570760549798248448)), (295/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-119768191/39614081257132168796771975168), (-276105219/316912650057057350374175801344)), (33/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((787/64), (7191/1024)), 0, by norm_num⟩
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
  | 0 => ⟨((12894208/210268945), (-7363584/210268945)), 0, by norm_num⟩
  | 1 => ⟨((-56019115311104/44213029231413025), (94947583721472/44213029231413025)), 0, by norm_num⟩
  | 2 => ⟨((21920263/17592186044416), (-1548650737/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((211557163/140737488355328), (382938839/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-844277123/9007199254740992), (-257184843/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1116580613/288230376151711744), (15807725/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1113258123/9223372036854775808), (594619729/9223372036854775808)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((379553889/147573952589676412928), (-603597271/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-68393565/9444732965739290427392), (1609791415/9444732965739290427392)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-208722281/75557863725914323419136), (-808891949/151115727451828646838272)), (3/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((862815825/4835703278458516698824704), (559750405/4835703278458516698824704)), (19/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-580098819/77371252455336267181195264), (-65753607/154742504910672534362390528)), (15/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((1175181575/4951760157141521099596496896), (-585564137/4951760157141521099596496896)), (93/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((787/64), (7191/1024)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((787/64), (7191/1024)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((787/64), (7191/1024)))⁻¹=value ((12894208/210268945), (-7363584/210268945)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((12894208/210268945), (-7363584/210268945))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-843805321/1180591620717411303424), (1120130477/1180591620717411303424)), (11/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-114480115/590295810358705651712), (-810028679/1180591620717411303424)), (97/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((15930775/73786976294838206464), (390268477/4722366482869645213696)), (71/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-851847693/18889465931478580854784), (549359375/18889465931478580854784)), (73/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((9631335/18889465931478580854784), (-753059457/75557863725914323419136)), (123/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((93771631/75557863725914323419136), (590094603/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-1019596479/4835703278458516698824704), (78096617/1208925819614629174706176)), (121/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((159923781/19342813113834066795298816), (-257334017/9671406556917033397649408)), (73/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((630164731/309485009821345068724781056), (780376013/309485009821345068724781056)), (163/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-1732711831/4951760157141521099596496896), (42332383/1237940039285380274899124224)), (341/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((652279903/39614081257132168796771975168), (-632353553/19807040628566084398385987584)), (85/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((278720865/158456325028528675187087900672), (476444377/158456325028528675187087900672)), (321/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-408807391/1267650600228229401496703205376), (-22666645/2535301200456458802993406410752)), (291/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19940765/4398046511104), (422236001/2199023255552)), (721/4398046511104), by norm_num⟩
  | 1 => ⟨((-79368391/549755813888), (810809741/4398046511104)), (763/2199023255552), by norm_num⟩
  | 2 => ⟨((-1181840395/8796093022208), (333775177/8796093022208)), (1649/4398046511104), by norm_num⟩
  | 3 => ⟨((-224476239/4398046511104), (-321238749/17592186044416)), (4849/17592186044416), by norm_num⟩
  | 4 => ⟨((-79204491/8796093022208), (-439647245/35184372088832)), (2721/17592186044416), by norm_num⟩
  | 5 => ⟨((-81475039/562949953421312), (-960129193/281474976710656)), (19835/281474976710656), by norm_num⟩
  | 6 => ⟨((680220507/2251799813685248), (-603820231/1125899906842624)), (30503/1125899906842624), by norm_num⟩
  | 7 => ⟨((721134521/9007199254740992), (-428241575/9007199254740992)), (81333/9007199254740992), by norm_num⟩
  | 8 => ⟨((1747587007/144115188075855872), (-94203489/144115188075855872)), (191849/72057594037927936), by norm_num⟩
  | 9 => ⟨((1497598309/1152921504606846976), (151540697/288230376151711744)), (813375/1152921504606846976), by norm_num⟩
  | 10 => ⟨((479700589/4611686018427387904), (952443107/9223372036854775808)), (784477/4611686018427387904), by norm_num⟩
  | 11 => ⟨((107543195/18446744073709551616), (59453547/4611686018427387904)), (1390941/36893488147419103232), by norm_num⟩
  | 12 => ⟨((125583063/1180591620717411303424), (1496049747/1180591620717411303424)), (285725/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19940765/4398046511104), (422236001/2199023255552)), (1443/8796093022208), by norm_num⟩
  | 1 => ⟨((-79368391/549755813888), (810809741/4398046511104)), (1527/4398046511104), by norm_num⟩
  | 2 => ⟨((-1181840395/8796093022208), (333775177/8796093022208)), (3299/8796093022208), by norm_num⟩
  | 3 => ⟨((-224476239/4398046511104), (-321238749/17592186044416)), (2425/8796093022208), by norm_num⟩
  | 4 => ⟨((-79204491/8796093022208), (-439647245/35184372088832)), (10887/70368744177664), by norm_num⟩
  | 5 => ⟨((-81475039/562949953421312), (-960129193/281474976710656)), (39693/562949953421312), by norm_num⟩
  | 6 => ⟨((680220507/2251799813685248), (-603820231/1125899906842624)), (61097/2251799813685248), by norm_num⟩
  | 7 => ⟨((721134521/9007199254740992), (-428241575/9007199254740992)), (40847/4503599627370496), by norm_num⟩
  | 8 => ⟨((1747587007/144115188075855872), (-94203489/144115188075855872)), (389463/144115188075855872), by norm_num⟩
  | 9 => ⟨((1497598309/1152921504606846976), (151540697/288230376151711744)), (214873/288230376151711744), by norm_num⟩
  | 10 => ⟨((479700589/4611686018427387904), (952443107/9223372036854775808)), (1937889/9223372036854775808), by norm_num⟩
  | 11 => ⟨((107543195/18446744073709551616), (59453547/4611686018427387904)), (2866681/36893488147419103232), by norm_num⟩
  | 12 => ⟨((125583063/1180591620717411303424), (1496049747/1180591620717411303424)), (56366865/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile040Gamma
