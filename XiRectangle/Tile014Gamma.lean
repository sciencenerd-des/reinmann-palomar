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
namespace Reinmann.XiRectangle.Tile014Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4089/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4089/640))
  have he : value ((3/4), (4089/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/309814321), (-5233920/309814321)), 0, by norm_num⟩
  | 1 => ⟨((-226405973196800/95984913496691041), (114694029312000/95984913496691041)), 0, by norm_num⟩
  | 2 => ⟨((161245823/2199023255552), (-35006066575/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-9313333499/4503599627370496), (50774131201/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((14217726729/288230376151711744), (-67530769637/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-13926922743/18446744073709551616), (21027706619/4611686018427387904)), (7/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-6974000285/590295810358705651712), (-98952864431/590295810358705651712)), (11/590295810358705651712), by norm_num⟩
  | 7 => ⟨((17319711411/9444732965739290427392), (55050060269/9444732965739290427392)), (9/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-269381043/2361183241434822606848), (-57618770529/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((54596309701/9671406556917033397649408), (27943577981/4835703278458516698824704)), (19/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-38446527347/154742504910672534362390528), (-12122565033/77371252455336267181195264)), (27/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((50063477489/4951760157141521099596496896), (34092371997/9903520314283042199192993792)), (39/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-122529069959/316912650057057350374175801344), (-11518131509/316912650057057350374175801344)), (7/39614081257132168796771975168), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (4089/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (4089/1280)))⁻¹=value ((21913600/309814321), (-5233920/309814321)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/309814321), (-5233920/309814321))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((90061220729/34359738368), (4027839927/17179869184)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((10956800/309814321), (-2616960/309814321)), 0, by norm_num⟩
  | 2 => ⟨((-56601493299200/95984913496691041), (28673507328000/95984913496691041)), 0, by norm_num⟩
  | 3 => ⟨((55038574251/4503599627370496), (-46674755433/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-9313333499/36028797018963968), (50774131201/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((11374181383/2305843009213693952), (-27012307855/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-4642307581/73786976294838206464), (112147768635/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-996285755/1180591620717411303424), (-113088987921/9444732965739290427392)), (13/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((17319711411/151115727451828646838272), (55050060269/151115727451828646838272)), (9/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-29931227/4722366482869645213696), (-51216684915/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((43677047761/154742504910672534362390528), (22354862385/77371252455336267181195264)), (1/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-13980555399/1237940039285380274899124224), (-8816410933/1237940039285380274899124224)), (21/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((66751303319/158456325028528675187087900672), (11364123999/79228162514264337593543950336)), (27/158456325028528675187087900672), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (87/20480)), 0, by norm_num⟩
  | 45 => ⟨((104110683233/4080638361600), (-172869/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-49350647919559/1915179604377600), (3576816060157/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((57787075077/2199023255552), (-13490779655/2199023255552)), (1/2199023255552), by norm_num⟩
  | 42 => ⟨((-59144843741/2199023255552), (13750994611/2199023255552)), (1/2199023255552), by norm_num⟩
  | 41 => ⟨((60592665601/2199023255552), (-14064775779/2199023255552)), (1/2199023255552), by norm_num⟩
  | 40 => ⟨((-31054208865/1099511627776), (14405325013/2199023255552)), (1/1099511627776), by norm_num⟩
  | 39 => ⟨((63698732657/2199023255552), (-7381914359/1099511627776)), (1/2199023255552), by norm_num⟩
  | 38 => ⟨((-32685943427/1099511627776), (15140165153/2199023255552)), (1/2199023255552), by norm_num⟩
  | 37 => ⟨((33567638989/1099511627776), (-7767983405/1099511627776)), (1/1099511627776), by norm_num⟩
  | 36 => ⟨((-68996477647/2199023255552), (7976489261/1099511627776)), (1/2199023255552), by norm_num⟩
  | 35 => ⟨((70963827461/2199023255552), (-1024562393/137438953472)), (1/2199023255552), by norm_num⟩
  | 34 => ⟨((-9130832617/274877906944), (16857986559/2199023255552)), (1/2199023255552), by norm_num⟩
  | 33 => ⟨((75255450855/2199023255552), (-17350128487/2199023255552)), (1/2199023255552), by norm_num⟩
  | 32 => ⟨((-9700247333/274877906944), (4467968387/549755813888)), (1/2199023255552), by norm_num⟩
  | 31 => ⟨((20024885629/549755813888), (-18425975873/2199023255552)), (1/2199023255552), by norm_num⟩
  | 30 => ⟨((-82763209145/2199023255552), (19015542397/2199023255552)), (1/1099511627776), by norm_num⟩
  | 29 => ⟨((5350632381/137438953472), (-19644091047/2199023255552)), (1/1099511627776), by norm_num⟩
  | 28 => ⟨((-88659850921/2199023255552), (5078905259/549755813888)), (1/1099511627776), by norm_num⟩
  | 27 => ⟨((91934882161/2199023255552), (-5258674525/549755813888)), (1/1099511627776), by norm_num⟩
  | 26 => ⟨((-23865283525/549755813888), (10903279267/1099511627776)), (1/1099511627776), by norm_num⟩
  | 25 => ⟨((49634332121/1099511627776), (-5659309253/549755813888)), (1/1099511627776), by norm_num⟩
  | 24 => ⟨((-103392524143/2199023255552), (11766862413/1099511627776)), (1/1099511627776), by norm_num⟩
  | 23 => ⟨((13484230193/274877906944), (-6126041829/549755813888)), (1/1099511627776), by norm_num⟩
  | 22 => ⟨((-56380598319/1099511627776), (12779056159/1099511627776)), (1/1099511627776), by norm_num⟩
  | 21 => ⟨((29528097541/549755813888), (-13353412853/1099511627776)), (1/1099511627776), by norm_num⟩
  | 20 => ⟨((-61998369979/1099511627776), (6990924045/549755813888)), (1/549755813888), by norm_num⟩
  | 19 => ⟨((32624524975/549755813888), (-14672380099/1099511627776)), (1/549755813888), by norm_num⟩
  | 18 => ⟨((-17214860133/274877906944), (15434695429/1099511627776)), (1/549755813888), by norm_num⟩
  | 17 => ⟨((36446371491/549755813888), (-4070151721/274877906944)), (1/549755813888), by norm_num⟩
  | 16 => ⟨((-77427885665/1099511627776), (1076541947/68719476736)), (1/549755813888), by norm_num⟩
  | 15 => ⟨((82564740785/1099511627776), (-18285035135/1099511627776)), (1/549755813888), by norm_num⟩
  | 14 => ⟨((-88431565367/1099511627776), (19484616363/1099511627776)), (1/549755813888), by norm_num⟩
  | 13 => ⟨((95195857723/1099511627776), (-20852782313/1099511627776)), (1/549755813888), by norm_num⟩
  | 12 => ⟨((-51540305171/549755813888), (2803474187/137438953472)), (1/549755813888), by norm_num⟩
  | 11 => ⟨((56194686105/549755813888), (-6065112327/274877906944)), (1/549755813888), by norm_num⟩
  | 10 => ⟨((-15443280805/137438953472), (13209845035/549755813888)), (1/549755813888), by norm_num⟩
  | 9 => ⟨((34290589213/274877906944), (-14500750985/549755813888)), (1/549755813888), by norm_num⟩
  | 8 => ⟨((-19268970609/137438953472), (16071824311/549755813888)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((10996616905/68719476736), (-18025615867/549755813888)), (1/274877906944), by norm_num⟩
  | 6 => ⟨((-102460066595/549755813888), (20521845777/549755813888)), (1/549755813888), by norm_num⟩
  | 5 => ⟨((15332957825/68719476736), (-372247783/8589934592)), (1/274877906944), by norm_num⟩
  | 4 => ⟨((-38201707979/137438953472), (3549926023/68719476736)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((6332863563/17179869184), (-17584207695/274877906944)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((-75275944507/137438953472), (5778859907/68719476736)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((36870329887/34359738368), (-8462824113/68719476736)), (1/68719476736), by norm_num⟩
  | 0 => ⟨((-20816809477/137438953472), (64445438835/274877906944)), (1/137438953472), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (4089/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (4089/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (4089/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((90061220729/34359738368), (4027839927/17179869184)), (1/34359738368), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (4089/1280))) (z:=((-21/128), (4089/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((90061220729/34359738368), (4027839927/17179869184))) (r:=(1/34359738368)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((70862755991/2147483648), (24463766385/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((123205802935/68719476736), (4172955977/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((876944134732800/95984913496691041), (-217029675035040/95984913496691041)), 0, by norm_num⟩
  | 3 => ⟨((-29383858427/281474976710656), (7736361937/140737488355328)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((59695241001/36028797018963968), (-53021521833/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-16323106271/576460752303423488), (47372381923/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((16326152071/36893488147419103232), (-43025646013/36893488147419103232)), (73/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-9614703001/2361183241434822606848), (78220562713/2361183241434822606848)), (93/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-4157535437/37778931862957161709568), (-70307009031/75557863725914323419136)), (63/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((23057693145/2417851639229258349412352), (30868779065/1208925819614629174706176)), (85/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-35438923101/77371252455336267181195264), (-52150779123/77371252455336267181195264)), (225/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((2859105065/154742504910672534362390528), (20666287203/1237940039285380274899124224)), (149/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-3373081681/4951760157141521099596496896), (-29192491153/79228162514264337593543950336)), (193/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((42140162199/2147483648), (35207125525/4294967296)), (5/4294967296), by norm_num⟩
  | 1 => ⟨((88846064567/68719476736), (4172955977/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((876944134732800/95984913496691041), (-217029675035040/95984913496691041)), 0, by norm_num⟩
  | 3 => ⟨((-29383858427/281474976710656), (7736361937/140737488355328)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((59695241001/36028797018963968), (-53021521833/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-16323106271/576460752303423488), (47372381923/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((16326152071/36893488147419103232), (-43025646013/36893488147419103232)), (73/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-9614703001/2361183241434822606848), (78220562713/2361183241434822606848)), (93/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-4157535437/37778931862957161709568), (-70307009031/75557863725914323419136)), (63/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((23057693145/2417851639229258349412352), (30868779065/1208925819614629174706176)), (85/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-35438923101/77371252455336267181195264), (-52150779123/77371252455336267181195264)), (225/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((2859105065/154742504910672534362390528), (20666287203/1237940039285380274899124224)), (149/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-3373081681/4951760157141521099596496896), (-29192491153/79228162514264337593543950336)), (193/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((88227135345/4294967296), (35207125525/4294967296)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((88846064567/68719476736), (4172955977/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((876944134732800/95984913496691041), (-217029675035040/95984913496691041)), 0, by norm_num⟩
  | 3 => ⟨((-29383858427/281474976710656), (7736361937/140737488355328)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((59695241001/36028797018963968), (-53021521833/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-16323106271/576460752303423488), (47372381923/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((16326152071/36893488147419103232), (-43025646013/36893488147419103232)), (73/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-9614703001/2361183241434822606848), (78220562713/2361183241434822606848)), (93/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-4157535437/37778931862957161709568), (-70307009031/75557863725914323419136)), (63/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((23057693145/2417851639229258349412352), (30868779065/1208925819614629174706176)), (85/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-35438923101/77371252455336267181195264), (-52150779123/77371252455336267181195264)), (225/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((2859105065/154742504910672534362390528), (20666287203/1237940039285380274899124224)), (149/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-3373081681/4951760157141521099596496896), (-29192491153/79228162514264337593543950336)), (193/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((452811946393600/95984913496691041), (-229388058624000/95984913496691041)), 0, by norm_num⟩
  | 1 => ⟨((-161245823/549755813888), (35006066575/140737488355328)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((27940000497/2251799813685248), (-38080598401/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-28435453457/72057594037927936), (67530769637/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((4352163357/576460752303423488), (-52569266547/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 5 => ⟨((2615250107/18446744073709551616), (74214648323/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-15154747485/590295810358705651712), (-96337605471/1180591620717411303424)), (3/295147905179352825856), by norm_num⟩
  | 7 => ⟨((269381043/147573952589676412928), (57618770529/18889465931478580854784)), (11/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-30710424207/302231454903657293676544), (-62873050457/604462909807314587353088)), (17/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((3003634949/604462909807314587353088), (15153206291/4835703278458516698824704)), (7/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-17209320387/77371252455336267181195264), (-5859626437/77371252455336267181195264)), (21/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((91896802469/9903520314283042199192993792), (1079824829/1237940039285380274899124224)), (1/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-115196076047/316912650057057350374175801344), (8159317951/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((161245823/549755813888), (-35006066575/140737488355328)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-27940000497/1125899906842624), (38080598401/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((21326590093/18014398509481984), (-12662019307/4503599627370496)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((-4352163357/144115188075855872), (52569266547/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((-1634531317/2305843009213693952), (-92768310403/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 5 => ⟨((5683030307/36893488147419103232), (72253204103/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-1885667301/147573952589676412928), (-50416424213/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((61420848415/75557863725914323419136), (62873050457/75557863725914323419136)), (15/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-27032714541/604462909807314587353088), (-34094714155/1208925819614629174706176)), (13/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((86046601935/38685626227668133590597632), (29298132185/38685626227668133590597632)), (23/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-31589525849/309485009821345068724781056), (-5939036559/618970019642690137449562112)), (19/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((86397057035/19807040628566084398385987584), (-6119488463/9903520314283042199192993792)), (15/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-55106077813/316912650057057350374175801344), (21702320669/316912650057057350374175801344)), (3/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9313333499/562949953421312), (-50774131201/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-28435453457/18014398509481984), (67530769637/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 2 => ⟨((4352163357/72057594037927936), (-105138533095/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 3 => ⟨((8717500357/4611686018427387904), (61845540269/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((-4735858589/9223372036854775808), (-60211003419/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 5 => ⟨((30170676817/590295810358705651712), (12604106053/147573952589676412928)), (1/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-17914414121/4722366482869645213696), (-9168986525/2361183241434822606848)), (9/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((9010904847/37778931862957161709568), (45459618873/302231454903657293676544)), (1/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-64534951451/4835703278458516698824704), (-10986799569/2417851639229258349412352)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((13162302437/19342813113834066795298816), (9898394265/154742504910672534362390528)), (29/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((-39598651141/1237940039285380274899124224), (11219062183/2475880078570760549798248448)), (25/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((55106077813/39614081257132168796771975168), (-21702320669/39614081257132168796771975168)), (11/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-35310967325/633825300114114700748351602688), (49319655369/1267650600228229401496703205376)), (9/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((14217726729/18014398509481984), (-67530769637/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4352163357/72057594037927936), (52569266547/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 2 => ⟨((-1634531317/576460752303423488), (-23192077601/576460752303423488)), (3/1152921504606846976), by norm_num⟩
  | 3 => ⟨((4735858589/4611686018427387904), (60211003419/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-9428336505/73786976294838206464), (-31510265133/147573952589676412928)), (9/295147905179352825856), by norm_num⟩
  | 5 => ⟨((53743242363/4722366482869645213696), (55013919149/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-63076333929/75557863725914323419136), (-19888583257/37778931862957161709568)), (15/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((64534951451/1208925819614629174706176), (10986799569/604462909807314587353088)), (15/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-118460721933/38685626227668133590597632), (-2783923387/9671406556917033397649408)), (31/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((24749156963/154742504910672534362390528), (-14023827729/618970019642690137449562112)), (31/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-75770856993/9903520314283042199192993792), (29840690921/9903520314283042199192993792)), (29/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((13241612747/39614081257132168796771975168), (-36989741527/158456325028528675187087900672)), (27/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-16647980537/1267650600228229401496703205376), (9363032357/633825300114114700748351602688)), (23/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13926922743/576460752303423488), (-21027706619/144115188075855872)), (7/576460752303423488), by norm_num⟩
  | 1 => ⟨((2615250107/1152921504606846976), (74214648323/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-5683030307/4611686018427387904), (-72253204103/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 3 => ⟨((1885667301/9223372036854775808), (12604106053/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-53743242363/2361183241434822606848), (-55013919149/2361183241434822606848)), (3/590295810358705651712), by norm_num⟩
  | 5 => ⟨((75691600715/37778931862957161709568), (5966574977/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-1411702063/9444732965739290427392), (-15381519397/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((47384288773/4835703278458516698824704), (4454277419/4835703278458516698824704)), (25/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-89096965067/154742504910672534362390528), (3155361239/38685626227668133590597632)), (27/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((75770856993/2475880078570760549798248448), (-29840690921/2475880078570760549798248448)), (29/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-29131548043/19807040628566084398385987584), (1271522365/1237940039285380274899124224)), (29/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((39955153289/633825300114114700748351602688), (-22471277657/316912650057057350374175801344)), (7/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-46848291157/20282409603651670423947251286016), (87353738359/20282409603651670423947251286016)), (13/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6974000285/9223372036854775808), (-98952864431/9223372036854775808)), (11/9223372036854775808), by norm_num⟩
  | 1 => ⟨((15154747485/18446744073709551616), (96337605471/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-30170676817/147573952589676412928), (-12604106053/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 3 => ⟨((17914414121/590295810358705651712), (36675946099/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-63076333929/18889465931478580854784), (-39777166513/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((90348932031/302231454903657293676544), (30763038793/302231454903657293676544)), (21/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-110563340471/4835703278458516698824704), (-5196656989/2417851639229258349412352)), (29/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((118795953423/77371252455336267181195264), (-16828593275/77371252455336267181195264)), (37/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-7103517843/77371252455336267181195264), (22380518191/618970019642690137449562112)), (11/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((6069072509/1237940039285380274899124224), (-33907263067/9903520314283042199192993792)), (25/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-36625557181/158456325028528675187087900672), (41197342371/158456325028528675187087900672)), (13/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((11712072789/1267650600228229401496703205376), (-10919217295/633825300114114700748351602688)), (13/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-22054974075/81129638414606681695789005144064), (83641133773/81129638414606681695789005144064)), (51/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-17319711411/73786976294838206464), (-55050060269/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 1 => ⟨((34480773505/295147905179352825856), (57618770529/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-61420848415/2361183241434822606848), (-7859131307/295147905179352825856)), (15/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((9010904847/2361183241434822606848), (5682452359/2361183241434822606848)), (9/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-64534951451/151115727451828646838272), (-21973599137/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((47384288773/1208925819614629174706176), (4454277419/1208925819614629174706176)), (13/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-59397976711/19342813113834066795298816), (16828593275/38685626227668133590597632)), (19/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((64946448851/309485009821345068724781056), (-25577735075/309485009821345068724781056)), (13/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((-31212372903/2475880078570760549798248448), (21797526257/2475880078570760549798248448)), (1/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((1635069517/2475880078570760549798248448), (-58853346245/79228162514264337593543950336)), (19/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-18404685811/633825300114114700748351602688), (17158770035/316912650057057350374175801344)), (43/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((4726065873/5070602400912917605986812821504), (-71692400377/20282409603651670423947251286016)), (23/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-1595655581/324518553658426726783156020576256), (17069179621/81129638414606681695789005144064)), (23/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-269381043/9223372036854775808), (-57618770529/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((61420848415/4722366482869645213696), (62873050457/4722366482869645213696)), (17/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((-27032714541/9444732965739290427392), (-17047357077/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((64534951451/151115727451828646838272), (10986799569/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-118460721933/2417851639229258349412352), (-5567846773/1208925819614629174706176)), (9/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((44548482533/9671406556917033397649408), (-12621444957/19342813113834066795298816)), (31/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-7103517843/19342813113834066795298816), (22380518191/154742504910672534362390528)), (3/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((31212372903/1237940039285380274899124224), (-21797526257/1237940039285380274899124224)), (17/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-14715625653/9903520314283042199192993792), (66210014525/39614081257132168796771975168)), (11/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((1437866079/19807040628566084398385987584), (-85793850175/633825300114114700748351602688)), (55/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-12996681151/5070602400912917605986812821504), (49288525259/5070602400912917605986812821504)), (65/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((2393483371/162259276829213363391578010288128), (-51207538863/81129638414606681695789005144064)), (37/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((20811712205/2596148429267413814265248164610048), (97125286331/2596148429267413814265248164610048)), (79/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-54596309701/18889465931478580854784), (-27943577981/9444732965739290427392)), (19/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((3003634949/2361183241434822606848), (15153206291/18889465931478580854784)), (7/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((-86046601935/302231454903657293676544), (-3662266523/37778931862957161709568)), (25/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((13162302437/302231454903657293676544), (1237299283/302231454903657293676544)), (17/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((-24749156963/4835703278458516698824704), (7011913865/9671406556917033397649408)), (37/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((2367839281/4835703278458516698824704), (-14920345461/77371252455336267181195264)), (17/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((-48552580071/1237940039285380274899124224), (33907263067/1237940039285380274899124224)), (7/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((1635069517/618970019642690137449562112), (-58853346245/19807040628566084398385987584)), (43/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((-1437866079/9903520314283042199192993792), (42896925087/158456325028528675187087900672)), (29/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((7220378417/1267650600228229401496703205376), (-27382514033/1267650600228229401496703205376)), (39/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-2925368565/81129638414606681695789005144064), (125173983887/81129638414606681695789005144064)), (47/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((-13874474803/649037107316853453566312041152512), (-64750190887/649037107316853453566312041152512)), (7/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((14526633425/5192296858534827628530496329220096), (60836718023/10384593717069655257060992658440192)), (63/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-38446527347/151115727451828646838272), (-12122565033/75557863725914323419136)), (27/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((17209320387/151115727451828646838272), (5859626437/151115727451828646838272)), (23/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-31589525849/1208925819614629174706176), (-5939036559/2417851639229258349412352)), (11/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((39598651141/9671406556917033397649408), (-1402382773/2417851639229258349412352)), (1/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((-2367839281/4835703278458516698824704), (14920345461/77371252455336267181195264)), (37/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((58263096085/1237940039285380274899124224), (-40688715681/1237940039285380274899124224)), (37/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-9156389295/2475880078570760549798248448), (10299335593/2475880078570760549798248448)), (1/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((18404685811/79228162514264337593543950336), (-17158770035/39614081257132168796771975168)), (51/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((-12996681151/1267650600228229401496703205376), (49288525259/1267650600228229401496703205376)), (73/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((731342141/10141204801825835211973625643008), (-125173983887/40564819207303340847894502572032)), (51/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((15261922283/324518553658426726783156020576256), (8903151247/40564819207303340847894502572032)), (33/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((-34863920219/5192296858534827628530496329220096), (-73004061627/5192296858534827628530496329220096)), (81/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((13564044407/20769187434139310514121985316880384), (67095565029/83076749736557242056487941267521536)), (95/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/929442963), (-436160/309814321)), 0, by norm_num⟩
  | 1 => ⟨((-56601493299200/287954740490073123), (9557835776000/95984913496691041)), 0, by norm_num⟩
  | 2 => ⟨((55038574251/9007199254740992), (-46674755433/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-49671111995/288230376151711744), (67698841601/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((4739242243/1152921504606846976), (-90041026183/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-4642307581/73786976294838206464), (112147768635/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 6 => ⟨((-4649333523/4722366482869645213696), (-65968576287/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 7 => ⟨((5773237137/37778931862957161709568), (73400080359/151115727451828646838272)), (13/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-89793681/9444732965739290427392), (-19206256843/1208925819614629174706176)), (9/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((36397539801/77371252455336267181195264), (37258103975/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-51262036463/2475880078570760549798248448), (-4040855011/309485009821345068724781056)), (19/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((66751303319/79228162514264337593543950336), (11364123999/39614081257132168796771975168)), (27/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-81686046639/2535301200456458802993406410752), (-7678754339/2535301200456458802993406410752)), (19/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44126225549/2147483648), (35201079023/4294967296)), (7/4294967296), by norm_num⟩
  | 1 => ⟨((44416278401/34359738368), (8352754795/68719476736)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((80417233903/8796093022208), (-2491782577/1099511627776)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-58864730745/562949953421312), (1942354503/35184372088832)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((59843342321/36028797018963968), (-3335827787/2251799813685248)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-16359374299/576460752303423488), (5976307393/144115188075855872)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((16289829153/36893488147419103232), (-43541025515/36893488147419103232)), (37/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-289183615/73786976294838206464), (79367438969/2361183241434822606848)), (47/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-4516710161/37778931862957161709568), (-17876850021/18889465931478580854784)), (127/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((3024389533/302231454903657293676544), (62901873879/2417851639229258349412352)), (171/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-9260215435/19342813113834066795298816), (-13290248219/19342813113834066795298816)), (227/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((47831659269/2475880078570760549798248448), (10510708039/618970019642690137449562112)), (75/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-56521995853/79228162514264337593543950336), (-14716226113/39614081257132168796771975168)), (97/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-29353906267/36028797018963968), (12446601449/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 1 => ⟨((9934222399/144115188075855872), (-54159073281/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 2 => ⟨((-15165575177/4611686018427387904), (36016410473/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((6189743441/73786976294838206464), (-74765179089/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 4 => ⟨((1162333381/590295810358705651712), (65968576287/2361183241434822606848)), (3/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-32330127969/75557863725914323419136), (-51380056251/37778931862957161709568)), (3/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((42909407027/1208925819614629174706176), (71703358881/1208925819614629174706176)), (7/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-21838523881/9671406556917033397649408), (-44709724769/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((38446527347/309485009821345068724781056), (12122565033/154742504910672534362390528)), (5/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-61188694709/9903520314283042199192993792), (-5208556833/2475880078570760549798248448)), (9/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((11231831413/39614081257132168796771975168), (8446629773/316912650057057350374175801344)), (7/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-61437907225/5070602400912917605986812821504), (8703272481/5070602400912917605986812821504)), (11/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((78373088445/162259276829213363391578010288128), (-30865522729/162259276829213363391578010288128)), (35/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((88252447599/4294967296), (35201081991/4294967296)), (1/536870912), by norm_num⟩
  | 1 => ⟨((88832561539/68719476736), (8352748339/68719476736)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((80417204977/8796093022208), (-1245886995/549755813888)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-58864683521/562949953421312), (31077386841/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((3740213329/2251799813685248), (-53372237991/36028797018963968)), (19/36028797018963968), by norm_num⟩
  | 5 => ⟨((-32719241917/1152921504606846976), (47808891149/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 6 => ⟨((4072784661/9223372036854775808), (-21769418651/18446744073709551616)), (75/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-9259207351/2361183241434822606848), (79361981239/2361183241434822606848)), (95/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-9024033963/75557863725914323419136), (-71501480863/75557863725914323419136)), (1/590295810358705651712), by norm_num⟩
  | 9 => ⟨((12090088809/1208925819614629174706176), (31448393699/1208925819614629174706176)), (43/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-37018924569/77371252455336267181195264), (-53158930711/77371252455336267181195264)), (57/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((47801660291/2475880078570760549798248448), (42047081801/2475880078570760549798248448)), (301/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-56483727743/79228162514264337593543950336), (-14723761641/39614081257132168796771975168)), (389/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11554723945/18446744073709551616), (-13720537323/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-884249063/18446744073709551616), (85445918959/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-5313524027/2361183241434822606848), (-37696329307/1180591620717411303424)), (3/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((1924412379/2361183241434822606848), (97866773811/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((-29931227/295147905179352825856), (-51216684915/302231454903657293676544)), (1/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((21838523881/2417851639229258349412352), (44709724769/4835703278458516698824704)), (5/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((-51262036463/77371252455336267181195264), (-4040855011/9671406556917033397649408)), (13/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((819491447/19342813113834066795298816), (17857909141/1237940039285380274899124224)), (13/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-48136420341/19807040628566084398385987584), (-9049960471/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((40227201159/316912650057057350374175801344), (-11397142535/633825300114114700748351602688)), (13/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-61578855207/10141204801825835211973625643008), (24251482145/10141204801825835211973625643008)), (3/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((10761437661/40564819207303340847894502572032), (-30061504225/162259276829213363391578010288128)), (23/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-13529787357/1298074214633706907132624082305024), (60874572277/5192296858534827628530496329220096)), (19/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44126223801/2147483648), (35201081985/4294967296)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((694004387/536870912), (8352748359/68719476736)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((80417204957/8796093022208), (-19934192201/8796093022208)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-29432341531/281474976710656), (31077388299/562949953421312)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((29921704805/18014398509481984), (-53372244097/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-2044951969/72057594037927936), (47808901809/1152921504606846976)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((32582228401/73786976294838206464), (-87077705433/73786976294838206464)), (19/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-9259107315/2361183241434822606848), (19840503825/590295810358705651712)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-9024217589/75557863725914323419136), (-17875374531/18889465931478580854784)), (129/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((24180484527/2417851639229258349412352), (62896743921/2417851639229258349412352)), (173/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-18509697189/38685626227668133590597632), (-53158745687/77371252455336267181195264)), (229/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((47802317117/2475880078570760549798248448), (42046623099/2475880078570760549798248448)), (151/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-882571149/1237940039285380274899124224), (-14723297205/39614081257132168796771975168)), (195/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8501638443/18889465931478580854784), (120628253783/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((-18474358839/37778931862957161709568), (-58720064287/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((36779491739/302231454903657293676544), (61460021897/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-21838523881/1208925819614629174706176), (-1397178899/75557863725914323419136)), (3/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((38446527347/19342813113834066795298816), (24245130065/19342813113834066795298816)), (9/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-27534912619/154742504910672534362390528), (-9375402299/154742504910672534362390528)), (7/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((33695494239/2475880078570760549798248448), (6334972329/4951760157141521099596496896)), (19/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((-36204481043/39614081257132168796771975168), (5128714141/39614081257132168796771975168)), (3/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((69276212107/1267650600228229401496703205376), (-13641458707/633825300114114700748351602688)), (7/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((-59187907135/20282409603651670423947251286016), (20667284155/10141204801825835211973625643008)), (1/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((22324149139/162259276829213363391578010288128), (-3138845133/20282409603651670423947251286016)), (33/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-28555148895/5192296858534827628530496329220096), (53244183381/5192296858534827628530496329220096)), (33/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((13443031817/83076749736557242056487941267521536), (-25490631245/41538374868278621028243970633760768)), (63/166153499473114484112975882535043072), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44126223801/2147483648), (35201081985/4294967296)), (5/2147483648), by norm_num⟩
  | 1 => ⟨((694004387/536870912), (8352748359/68719476736)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((40208602479/4398046511104), (-19934192199/8796093022208)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-919760673/8796093022208), (31077388289/562949953421312)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((29921704841/18014398509481984), (-13343061013/9007199254740992)), (21/36028797018963968), by norm_num⟩
  | 5 => ⟨((-32719231709/1152921504606846976), (47808901739/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 6 => ⟨((32582229405/73786976294838206464), (-87077705339/73786976294838206464)), (77/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-9259109473/2361183241434822606848), (39681007803/1180591620717411303424)), (97/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-2256053365/18889465931478580854784), (-35750749875/37778931862957161709568)), (65/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((24180477471/2417851639229258349412352), (3931046803/151115727451828646838272)), (87/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-37019383733/77371252455336267181195264), (-53158757661/77371252455336267181195264)), (115/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((47802303501/2475880078570760549798248448), (5255831061/309485009821345068724781056)), (303/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-14121135179/19807040628566084398385987584), (-14723321515/39614081257132168796771975168)), (391/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7430200351/302231454903657293676544), (-1552020755/37778931862957161709568)), (3/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((52941876075/4835703278458516698824704), (54193605781/4835703278458516698824704)), (15/4835703278458516698824704), by norm_num⟩
  | 2 => ⟨((-23300925665/9671406556917033397649408), (-29388036443/19342813113834066795298816)), (13/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((55626086099/154742504910672534362390528), (2367525833/19342813113834066795298816)), (17/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((-102107558299/2475880078570760549798248448), (-4799221461/1237940039285380274899124224)), (1/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((38398692015/9903520314283042199192993792), (-10879090603/19807040628566084398385987584)), (7/4951760157141521099596496896), by norm_num⟩
  | 6 => ⟨((-97966360555/316912650057057350374175801344), (38581903413/316912650057057350374175801344)), (43/316912650057057350374175801344), by norm_num⟩
  | 7 => ⟨((3362949269/158456325028528675187087900672), (-37576880281/2535301200456458802993406410752)), (15/1267650600228229401496703205376), by norm_num⟩
  | 8 => ⟨((-12684175647/10141204801825835211973625643008), (28534955755/20282409603651670423947251286016)), (39/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((39659929021/649037107316853453566312041152512), (-9243781837/81129638414606681695789005144064)), (3/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-5601263257/2596148429267413814265248164610048), (84968770817/10384593717069655257060992658440192)), (57/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((1031534921/83076749736557242056487941267521536), (-88276969353/166153499473114484112975882535043072)), (65/166153499473114484112975882535043072), by norm_num⟩
  | 12 => ⟨((17938714897/2658455991569831745807614120560689152), (83717418521/2658455991569831745807614120560689152)), (69/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44126223801/2147483648), (35201081985/4294967296)), (11/4294967296), by norm_num⟩
  | 1 => ⟨((694004387/536870912), (8352748359/68719476736)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((40208602479/4398046511104), (-19934192199/8796093022208)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((-919760673/8796093022208), (31077388289/562949953421312)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((59843409681/36028797018963968), (-13343061013/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-32719231705/1152921504606846976), (23904450869/576460752303423488)), (15/576460752303423488), by norm_num⟩
  | 6 => ⟨((16291114691/36893488147419103232), (-43538852665/36893488147419103232)), (39/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-9259109423/2361183241434822606848), (79362015571/2361183241434822606848)), (49/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-9024213555/75557863725914323419136), (-17875374911/18889465931478580854784)), (131/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((24180477619/2417851639229258349412352), (62896748573/2417851639229258349412352)), (175/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-9254845975/19342813113834066795298816), (-13289689257/19342813113834066795298816)), (231/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((11950575883/618970019642690137449562112), (42046647173/2475880078570760549798248448)), (19/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-56484540181/79228162514264337593543950336), (-29446640535/79228162514264337593543950336)), (49/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((75491585099/154742504910672534362390528), (47606466069/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | 1 => ⟨((-8447829779/38685626227668133590597632), (-23011310427/309485009821345068724781056)), (3/38685626227668133590597632), by norm_num⟩
  | 2 => ⟨((124055073029/2475880078570760549798248448), (11661580765/2475880078570760549798248448)), (11/618970019642690137449562112), by norm_num⟩
  | 3 => ⟨((-9719229371/1237940039285380274899124224), (2753645277/2475880078570760549798248448)), (33/9903520314283042199192993792), by norm_num⟩
  | 4 => ⟨((74389840817/79228162514264337593543950336), (-29296807977/79228162514264337593543950336)), (37/79228162514264337593543950336), by norm_num⟩
  | 5 => ⟨((-57201180181/633825300114114700748351602688), (19973557135/316912650057057350374175801344)), (37/633825300114114700748351602688), by norm_num⟩
  | 6 => ⟨((17979005891/2535301200456458802993406410752), (-10111617655/1267650600228229401496703205376)), (33/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((-18069237991/40564819207303340847894502572032), (67384122191/81129638414606681695789005144064)), (51/81129638414606681695789005144064), by norm_num⟩
  | 8 => ⟨((3189950201/162259276829213363391578010288128), (-96780363683/1298074214633706907132624082305024)), (73/1298074214633706907132624082305024), by norm_num⟩
  | 9 => ⟨((-1436025079/10384593717069655257060992658440192), (30723133885/5192296858534827628530496329220096)), (101/20769187434139310514121985316880384), by norm_num⟩
  | 10 => ⟨((-14983755157/166153499473114484112975882535043072), (-17481760939/41538374868278621028243970633760768)), (33/83076749736557242056487941267521536), by norm_num⟩
  | 11 => ⟨((34228482801/2658455991569831745807614120560689152), (17918368417/664613997892457936451903530140172288)), (81/2658455991569831745807614120560689152), by norm_num⟩
  | 12 => ⟨((-26633646347/21267647932558653966460912964485513216), (-65872666619/42535295865117307932921825928971026432)), (47/21267647932558653966460912964485513216), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44126223801/2147483648), (35201081985/4294967296)), (3/1073741824), by norm_num⟩
  | 1 => ⟨((694004387/536870912), (8352748359/68719476736)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((40208602479/4398046511104), (-19934192199/8796093022208)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-919760673/8796093022208), (31077388289/562949953421312)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((59843409681/36028797018963968), (-13343061013/9007199254740992)), (23/36028797018963968), by norm_num⟩
  | 5 => ⟨((-32719231705/1152921504606846976), (23904450869/576460752303423488)), (31/1152921504606846976), by norm_num⟩
  | 6 => ⟨((32582229383/73786976294838206464), (-87077705331/73786976294838206464)), (79/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-578694339/147573952589676412928), (79362015573/2361183241434822606848)), (99/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-4512106777/37778931862957161709568), (-35750749825/37778931862957161709568)), (33/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((24180477619/2417851639229258349412352), (62896748587/2417851639229258349412352)), (11/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-37019383907/77371252455336267181195264), (-53158757061/77371252455336267181195264)), (29/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((11950575891/618970019642690137449562112), (5255830905/309485009821345068724781056)), (305/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-7060567535/9903520314283042199192993792), (-14723320329/39614081257132168796771975168)), (393/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-590029723451275/2097152), (828958560351897/1048576)), (3481245/524288), by norm_num⟩
  | 1 => ⟨((-29426246429/64), (15803875413/16)), (305/32), by norm_num⟩
  | 2 => ⟨((-45822498897/128), (39573843963/64)), (221/32), by norm_num⟩
  | 3 => ⟨((-23120934585/128), (66189392799/256)), (863/256), by norm_num⟩
  | 4 => ⟨((-34391902379/512), (41577032137/512)), (639/512), by norm_num⟩
  | 5 => ⟨((-5059608389/256), (41824298813/2048)), (191/512), by norm_num⟩
  | 6 => ⟨((-19712787737/4096), (17531679395/4096)), (769/8192), by norm_num⟩
  | 7 => ⟨((-65559189939/65536), (25170460283/32768)), (335/16384), by norm_num⟩
  | 8 => ⟨((-47588271005/262144), (31543673579/262144)), (1033/262144), by norm_num⟩
  | 9 => ⟨((-30678793357/1048576), (17493940047/1048576)), (1429/2097152), by norm_num⟩
  | 10 => ⟨((-71208691725/16777216), (34690718629/16777216)), (1797/16777216), by norm_num⟩
  | 11 => ⟨((-75192552529/134217728), (15474560619/67108864)), (519/33554432), by norm_num⟩
  | 12 => ⟨((-36442015655/536870912), (12462099717/536870912)), (2221/1073741824), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1610741667405865/10141204801825835211973625643008), (2491512167135/10141204801825835211973625643008)), (3641/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1814289682904303/633825300114114700748351602688), (3058661476845/633825300114114700748351602688)), (2241/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((482436592956057/9903520314283042199192993792), (3450244557249/39614081257132168796771975168)), (2529/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((120753901689579/154742504910672534362390528), (1836880490085/1237940039285380274899124224)), (2693/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((226721794627501/19342813113834066795298816), (3682572228545/154742504910672534362390528)), (675/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((49672632820479/302231454903657293676544), (3461801562221/9671406556917033397649408)), (2539/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((646905952723921/302231454903657293676544), (1519250034729/302231454903657293676544)), (4459/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1944796433015301/75557863725914323419136), (2477651919315/37778931862957161709568)), (3637/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((167546648381783/590295810358705651712), (3732073577905/4722366482869645213696)), (5481/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1680475682568263/590295810358705651712), (5157080146895/590295810358705651712)), (947/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1897456671234581/73786976294838206464), (810601007315/9223372036854775808)), (2383/18446744073709551616), by norm_num⟩
  | 7 => ⟨((953079857592117/4611686018427387904), (7348680453641/9223372036854775808)), (10809/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1677751496676013/1152921504606846976), (463491393013/72057594037927936)), (10917/1152921504606846976), by norm_num⟩
  | 5 => ⟨((317066167686743/36028797018963968), (1641320474849/36028797018963968)), (2419/36028797018963968), by norm_num⟩
  | 4 => ⟨((1602948256380625/36028797018963968), (10002809001033/36028797018963968)), (14763/36028797018963968), by norm_num⟩
  | 3 => ⟨((1629785995565181/9007199254740992), (6389656320753/4503599627370496)), (4725/2251799813685248), by norm_num⟩
  | 2 => ⟨((157077427084469/281474976710656), (3300671844557/562949953421312)), (9793/1125899906842624), by norm_num⟩
  | 1 => ⟨((663714034731029/562949953421312), (20897107328925/1125899906842624)), (31155/1125899906842624), by norm_num⟩
  | 0 => ⟨((1551460140373251/1125899906842624), (46380778037269/1125899906842624)), (69797/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1551460140373251/1125899906842624), (46380778037269/1125899906842624)), (266254429343795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1067980100175901/562949953421312), (63911479135045/562949953421312)), (99055/562949953421312), by norm_num⟩
  | 2 => ⟨((504705973550345/140737488355328), (121247346188077/281474976710656)), (99583/140737488355328), by norm_num⟩
  | 3 => ⟨((222979759099563/17592186044416), (434811368409165/140737488355328)), (25001/4398046511104), by norm_num⟩
  | 4 => ⟨((332291676825635/2199023255552), (688900557446651/8796093022208)), (788255/4398046511104), by norm_num⟩
  | 5 => ⟨((286903869051429/17179869184), (406636362626611/17179869184)), (2825743/34359738368), by norm_num⟩
  | 6 => ⟨((-590029723451275/2097152), (828958560351897/1048576)), (3481245/524288), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((44126223801/2147483648), (35201081985/4294967296)), (3/1073741824), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/19817521), (-5233920/19817521)), 0, by norm_num⟩
  | 1 => ⟨((11159405363200/392734138585441), (11790974976000/392734138585441)), 0, by norm_num⟩
  | 2 => ⟨((-24539533687/4398046511104), (35989793559/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((6612925129/140737488355328), (-120061360157/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((61914298607/562949953421312), (15394748579/281474976710656)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-60679697903/4503599627370496), (12851855011/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-13358189501/18014398509481984), (-21869704103/9007199254740992)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((104562782683/288230376151711744), (361049745/9007199254740992)), (3/72057594037927936), by norm_num⟩
  | 8 => ⟨((-29875544195/1152921504606846976), (52604491535/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 9 => ⟨((-20993955235/4611686018427387904), (-55480926561/9223372036854775808)), (1/576460752303423488), by norm_num⟩
  | 10 => ⟨((77703582775/73786976294838206464), (-2391165197/9223372036854775808)), (25/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-15123847729/590295810358705651712), (45393051089/295147905179352825856)), (39/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-11128944729/590295810358705651712), (-3578650681/295147905179352825856)), (15/1180591620717411303424), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (4089/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (4089/1280)))⁻¹=value ((2252800/19817521), (-5233920/19817521)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/19817521), (-5233920/19817521))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/25961521), (-5233920/25961521)), 0, by norm_num⟩
  | 1 => ⟨((6126240563200/674000572633441), (20366229504000/674000572633441)), 0, by norm_num⟩
  | 2 => ⟨((-65567562699/17592186044416), (-23719291417/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((14609366443/35184372088832), (-4831744469/17592186044416)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-483025527/140737488355328), (70299008055/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-6796654803/1125899906842624), (-45262746489/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((8637374125/9007199254740992), (-4177674371/18014398509481984)), (11/72057594037927936), by norm_num⟩
  | 7 => ⟨((-6987862837/144115188075855872), (65740873579/576460752303423488)), (17/576460752303423488), by norm_num⟩
  | 8 => ⟨((-36256394309/4611686018427387904), (-61954235657/4611686018427387904)), (25/4611686018427387904), by norm_num⟩
  | 9 => ⟨((71697554951/36893488147419103232), (3953023745/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-49360612717/295147905179352825856), (13269455777/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-6604625647/1180591620717411303424), (-17906729093/590295810358705651712)), (37/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((65680187039/18889465931478580854784), (32290633889/18889465931478580854784)), (105/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (4089/1280)))⁻¹=value ((3891200/25961521), (-5233920/25961521)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/25961521), (-5233920/25961521))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18627823206400/514492987609441), (-32157204480000/514492987609441)), 0, by norm_num⟩
  | 1 => ⟨((84993505867/4398046511104), (-853841197/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-32590572049/17592186044416), (3731817811/1099511627776)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-51824540643/140737488355328), (-20351851101/35184372088832)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((127692801429/1125899906842624), (-2180003435/281474976710656)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-16746539345/2251799813685248), (9254849161/562949953421312)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-30632937751/18014398509481984), (-19780866917/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 7 => ⟨((29634627089/72057594037927936), (-10658422475/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 8 => ⟨((-20811445617/1152921504606846976), (68093050449/1152921504606846976)), (17/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-7489037401/1152921504606846976), (-57457438433/9223372036854775808)), (27/9223372036854775808), by norm_num⟩
  | 10 => ⟨((90043735953/73786976294838206464), (-32398777353/73786976294838206464)), (41/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-11821534905/590295810358705651712), (54346415635/295147905179352825856)), (1/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-52725802295/2361183241434822606848), (-8166383671/590295810358705651712)), (25/1180591620717411303424), by norm_num⟩
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
  | 0 => ⟨((27/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/3931369), (-1744640/11794107)), 0, by norm_num⟩
  | 1 => ⟨((-176808755200/139100959927449), (357302272000/15455662214161)), 0, by norm_num⟩
  | 2 => ⟨((-28332749021/17592186044416), (-66866514629/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((9373488051/35184372088832), (2067767001/70368744177664)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-51770851829/2251799813685248), (39199802071/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((18337626685/36028797018963968), (-110275122389/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((53786344661/288230376151711744), (79786172063/288230376151711744)), (11/288230376151711744), by norm_num⟩
  | 7 => ⟨((-20208154607/576460752303423488), (-18051070419/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((15302837407/4611686018427387904), (-36544381501/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-16641521021/147573952589676412928), (14765880367/36893488147419103232)), (23/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-12272388329/590295810358705651712), (-46768897723/1180591620717411303424)), (29/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((86033353477/18889465931478580854784), (3678331317/2361183241434822606848)), (71/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-35596690571/75557863725914323419136), (8127620645/37778931862957161709568)), (87/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (4089/1280)))⁻¹=value ((614400/3931369), (-1744640/11794107)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/3931369), (-1744640/11794107))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-65548699271/4398046511104), (-9702584359/2199023255552)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((9856938831/2199023255552), (-16037882989/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((4644241629/35184372088832), (49995119079/35184372088832)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-72768054211/281474976710656), (-19308957325/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((52835789865/1125899906842624), (-7427390095/281474976710656)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-4014256143/9007199254740992), (41442888117/4503599627370496)), (9/9007199254740992), by norm_num⟩
  | 6 => ⟨((-44546039459/36028797018963968), (-30397423709/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 7 => ⟨((61205078363/288230376151711744), (-28221832771/288230376151711744)), (13/288230376151711744), by norm_num⟩
  | 8 => ⟨((-990204711/288230376151711744), (81297585519/2305843009213693952)), (23/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-78876783009/18446744073709551616), (-55742480213/18446744073709551616)), (9/4611686018427387904), by norm_num⟩
  | 10 => ⟨((50424920295/73786976294838206464), (-24295644619/73786976294838206464)), (29/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-728834973/147573952589676412928), (15939892899/147573952589676412928)), (87/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-3878013891/295147905179352825856), (-36193887629/4722366482869645213696)), (17/1180591620717411303424), by norm_num⟩
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
  | 0 => ⟨((35/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/48079921), (-5233920/48079921)), 0, by norm_num⟩
  | 1 => ⟨((-11993152716800/2311678803366241), (37516738560000/2311678803366241)), 0, by norm_num⟩
  | 2 => ⟨((-17473056757/35184372088832), (-26250193297/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((66560790603/562949953421312), (47399443919/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-120664531801/9007199254740992), (358346643/2251799813685248)), (7/9007199254740992), by norm_num⟩
  | 5 => ⟨((35666495097/36028797018963968), (-53396345741/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((-9644053775/288230376151711744), (31451639461/288230376151711744)), (9/576460752303423488), by norm_num⟩
  | 7 => ⟨((-31776021379/9223372036854775808), (-358675659/36028797018963968)), (5/2305843009213693952), by norm_num⟩
  | 8 => ⟨((58931388491/73786976294838206464), (40920162897/73786976294838206464)), (11/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-105922478815/1180591620717411303424), (2516883537/1180591620717411303424)), (23/590295810358705651712), by norm_num⟩
  | 10 => ⟨((62069915719/9444732965739290427392), (-47623273051/9444732965739290427392)), (3/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-4069489935/18889465931478580854784), (55427095607/75557863725914323419136)), (25/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-28855383323/1208925819614629174706176), (-80282820823/1208925819614629174706176)), (13/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (4089/1280)))⁻¹=value ((7168000/48079921), (-5233920/48079921)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/48079921), (-5233920/48079921))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-95078055895/35184372088832), (33940221943/35184372088832)), (3/35184372088832), by norm_num⟩
  | 1 => ⟨((29570937835/70368744177664), (-5500166211/4398046511104)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((7427611555/35184372088832), (2758174097/8796093022208)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-97143750969/1125899906842624), (-4723669165/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 4 => ⟨((48565332395/4503599627370496), (-15116250011/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((15532305235/18014398509481984), (54190426993/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((-18164913755/36028797018963968), (-6070735099/36028797018963968)), (15/144115188075855872), by norm_num⟩
  | 7 => ⟨((39056909487/576460752303423488), (-3789894361/72057594037927936)), (13/576460752303423488), by norm_num⟩
  | 8 => ⟨((5248717765/4611686018427387904), (122104958933/9223372036854775808)), (21/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-65369228339/36893488147419103232), (-33570476703/36893488147419103232)), (35/36893488147419103232), by norm_num⟩
  | 10 => ⟨((18272829245/73786976294838206464), (-11222466735/73786976294838206464)), (7/36893488147419103232), by norm_num⟩
  | 11 => ⟨((123995383/147573952589676412928), (24472002293/590295810358705651712)), (43/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-24142226875/4722366482869645213696), (-26038307933/9444732965739290427392)), (67/9444732965739290427392), by norm_num⟩
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
  | 0 => ⟨((43/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/64054321), (-5233920/64054321)), 0, by norm_num⟩
  | 1 => ⟨((-25079381196800/4102956038771041), (46091993088000/4102956038771041)), 0, by norm_num⟩
  | 2 => ⟨((-2728771147/70368744177664), (-71914198521/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((50010529301/1125899906842624), (77312258509/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-13192847697/2251799813685248), (-26171009685/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((18787271099/36028797018963968), (-5711259727/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-78920592453/2305843009213693952), (13851366357/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 7 => ⟨((25292191093/18446744073709551616), (-7032989687/2305843009213693952)), (11/18446744073709551616), by norm_num⟩
  | 8 => ⟨((8960855761/295147905179352825856), (78415926737/295147905179352825856)), (5/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-15278768389/1180591620717411303424), (-20097367515/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((59883912525/37778931862957161709568), (24233832615/37778931862957161709568)), (33/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-81705604649/604462909807314587353088), (1561405731/75557863725914323419136)), (59/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((20424978209/2417851639229258349412352), (-16787111231/2417851639229258349412352)), (53/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (4089/1280)))⁻¹=value ((8806400/64054321), (-5233920/64054321)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/64054321), (-5233920/64054321))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-41193472959/140737488355328), (6217551731/17592186044416)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-5450940887/140737488355328), (-68265051041/281474976710656)), (7/281474976710656), by norm_num⟩
  | 2 => ⟨((75678780403/1125899906842624), (2881606483/70368744177664)), (5/562949953421312), by norm_num⟩
  | 3 => ⟨((-41655132785/2251799813685248), (28843007013/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((25139133761/18014398509481984), (-17667616865/4503599627370496)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((30890106865/72057594037927936), (48264787199/72057594037927936)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((-80657142583/576460752303423488), (-6051934487/576460752303423488)), (11/288230376151711744), by norm_num⟩
  | 7 => ⟨((17368069119/1152921504606846976), (-20477993459/1152921504606846976)), (9/1152921504606846976), by norm_num⟩
  | 8 => ⟨((17124598525/18446744073709551616), (65735590773/18446744073709551616)), (31/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-38911774573/73786976294838206464), (-27649211195/147573952589676412928)), (51/147573952589676412928), by norm_num⟩
  | 10 => ⟨((77358120095/1180591620717411303424), (-3675413431/73786976294838206464)), (81/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((9763701971/9444732965739290427392), (110807078179/9444732965739290427392)), (63/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-27928290989/18889465931478580854784), (-13705282925/18889465931478580854784)), (99/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((51/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/27768507), (-1744640/27768507)), 0, by norm_num⟩
  | 1 => ⟨((-1512961638400/257029993669683), (6074138624000/771089981009049)), 0, by norm_num⟩
  | 2 => ⟨((534596423/4398046511104), (-95524345729/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((15426910137/1125899906842624), (815724599/17592186044416)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-41713919803/18014398509481984), (-44610913619/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((16065765979/72057594037927936), (5944978159/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-38205247421/2305843009213693952), (2112016177/1152921504606846976)), (11/4611686018427387904), by norm_num⟩
  | 7 => ⟨((72396242903/73786976294838206464), (-2929966451/4611686018427387904)), (9/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-12263314883/295147905179352825856), (10426232867/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 9 => ⟨((7278358931/18889465931478580854784), (-54159203807/9444732965739290427392)), (43/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((2946436627/18889465931478580854784), (28076373287/75557863725914323419136)), (17/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-6483345967/302231454903657293676544), (-44475601917/2417851639229258349412352)), (13/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((74378720521/38685626227668133590597632), (18541124439/38685626227668133590597632)), (79/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (4089/1280)))⁻¹=value ((3481600/27768507), (-1744640/27768507)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/27768507), (-1744640/27768507))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-16317789023/1125899906842624), (70596234941/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 1 => ⟨((-47636138411/2251799813685248), (-72869256547/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((60091995095/4503599627370496), (5123632569/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 3 => ⟨((-50889217233/18014398509481984), (40383481179/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 4 => ⟨((1266939905/36028797018963968), (-116562632293/144115188075855872)), (23/144115188075855872), by norm_num⟩
  | 5 => ⟨((68618929819/576460752303423488), (62751097495/576460752303423488)), (13/288230376151711744), by norm_num⟩
  | 6 => ⟨((-4191485925/144115188075855872), (5060971875/1152921504606846976)), (25/2305843009213693952), by norm_num⟩
  | 7 => ⟨((45346026295/18446744073709551616), (-40234899483/9223372036854775808)), (21/9223372036854775808), by norm_num⟩
  | 8 => ⟨((23849030957/73786976294838206464), (54540468447/73786976294838206464)), (9/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-71645862355/590295810358705651712), (-489626335/18446744073709551616)), (15/147573952589676412928), by norm_num⟩
  | 10 => ⟨((63886904217/4722366482869645213696), (-29540627505/2361183241434822606848)), (95/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((15551234451/37778931862957161709568), (49401915947/18889465931478580854784)), (149/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-25608290211/75557863725914323419136), (-5632821981/37778931862957161709568)), (117/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((59/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/105833521), (-5233920/105833521)), 0, by norm_num⟩
  | 1 => ⟨((-59304901836800/11200734167257441), (63242502144000/11200734167257441)), 0, by norm_num⟩
  | 2 => ⟨((22889284423/140737488355328), (-31894393093/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((1082636233/562949953421312), (67318810627/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-30589031227/36028797018963968), (-59773948319/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((25793923863/288230376151711744), (42493911169/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-63931049837/9223372036854775808), (-9201461207/4611686018427387904)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((32836896169/73786976294838206464), (-8484556287/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-28313981115/1180591620717411303424), (33732372239/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((38376835673/37778931862957161709568), (-26607117203/18889465931478580854784)), (3/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-437469937/18889465931478580854784), (15946923375/151115727451828646838272)), (33/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-12450233721/9671406556917033397649408), (-63800527093/9671406556917033397649408)), (11/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((9153347905/38685626227668133590597632), (6668501577/19342813113834066795298816)), (59/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (4089/1280)))⁻¹=value ((12083200/105833521), (-5233920/105833521)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/105833521), (-5233920/105833521))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13026038331/9007199254740992), (17734162475/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 1 => ⟨((-77334512493/18014398509481984), (-55165177683/18014398509481984)), (19/18014398509481984), by norm_num⟩
  | 2 => ⟨((35249106929/18014398509481984), (-2985269439/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-45420544809/144115188075855872), (66718285387/144115188075855872)), (19/144115188075855872), by norm_num⟩
  | 4 => ⟨((-16971222567/576460752303423488), (-73962304963/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 5 => ⟨((54941390785/2305843009213693952), (15146915941/1152921504606846976)), (23/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-44166695075/9223372036854775808), (16405694761/9223372036854775808)), (45/18446744073709551616), by norm_num⟩
  | 7 => ⟨((21715672891/73786976294838206464), (-61948931603/73786976294838206464)), (5/9223372036854775808), by norm_num⟩
  | 8 => ⟨((45698453229/590295810358705651712), (72967367739/590295810358705651712)), (17/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-53471187975/2361183241434822606848), (-2562137315/1180591620717411303424)), (57/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((21461154653/9444732965739290427392), (-47856892193/18889465931478580854784)), (23/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((2063997877/18889465931478580854784), (18098130529/37778931862957161709568)), (145/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-77555335181/1208925819614629174706176), (-3763855085/151115727451828646838272)), (57/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((67/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/131638321), (-5233920/131638321)), 0, by norm_num⟩
  | 1 => ⟨((-80444193996800/17328647555699041), (71817756672000/17328647555699041)), 0, by norm_num⟩
  | 2 => ⟨((22455627497/140737488355328), (-10847018551/35184372088832)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-2462426695/1125899906842624), (86647687567/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-19347152163/72057594037927936), (-75388229057/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((40112929909/1152921504606846976), (14178024607/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-51488968185/18446744073709551616), (-17266487733/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((107841406673/590295810358705651712), (24838789707/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-97829317287/9444732965739290427392), (13589073861/9444732965739290427392)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((77257177087/151115727451828646838272), (-10612330071/37778931862957161709568)), (11/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-3182643657/151115727451828646838272), (59972231187/2417851639229258349412352)), (13/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((5847013971/9671406556917033397649408), (-4137997947/2417851639229258349412352)), (31/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((778060845/309485009821345068724781056), (31324934797/309485009821345068724781056)), (9/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (4089/1280)))⁻¹=value ((13721600/131638321), (-5233920/131638321)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/131638321), (-5233920/131638321))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16712909555/36028797018963968), (27505276149/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 1 => ⟨((-87707313865/144115188075855872), (-25808742539/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 2 => ⟨((16289638669/72057594037927936), (-33178617149/288230376151711744)), (11/144115188075855872), by norm_num⟩
  | 3 => ⟨((-13799955057/576460752303423488), (82181766299/1152921504606846976)), (7/288230376151711744), by norm_num⟩
  | 4 => ⟨((-19229646075/2305843009213693952), (-75606276021/4611686018427387904)), (31/4611686018427387904), by norm_num⟩
  | 5 => ⟨((69481246951/18446744073709551616), (1280620839/1152921504606846976)), (35/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-5965821813/9223372036854775808), (28982653725/73786976294838206464)), (35/73786976294838206464), by norm_num⟩
  | 7 => ⟨((6847065815/295147905179352825856), (-19560250721/147573952589676412928)), (1/9223372036854775808), by norm_num⟩
  | 8 => ⟨((34025415375/2361183241434822606848), (40555967047/2361183241434822606848)), (55/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-133712457145/37778931862957161709568), (1236566711/18889465931478580854784)), (183/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((24124731325/75557863725914323419136), (-64708754701/151115727451828646838272)), (75/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((26969520819/1208925819614629174706176), (89769578349/1208925819614629174706176)), (119/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-49886291171/4835703278458516698824704), (-4197588159/1208925819614629174706176)), (187/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((75/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/53573307), (-1744640/53573307)), 0, by norm_num⟩
  | 1 => ⟨((-1287257292800/318899913657361), (8932556800000/2870099222916249)), 0, by norm_num⟩
  | 2 => ⟨((20014323953/140737488355328), (-7545166029/35184372088832)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-14878736471/4503599627370496), (56578262877/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-3364297793/72057594037927936), (-23566866591/36028797018963968)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((29703329969/2305843009213693952), (35160080805/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-20515023737/18446744073709551616), (-23012774615/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 7 => ⟨((86721353909/1180591620717411303424), (48999969341/1180591620717411303424)), (1/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-39534661433/9444732965739290427392), (-3717608851/4722366482869645213696)), (9/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((64327332191/302231454903657293676544), (-9230100233/302231454903657293676544)), (5/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-46777435449/4835703278458516698824704), (186060651/37778931862957161709568)), (21/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((7389894231/19342813113834066795298816), (-60790421087/154742504910672534362390528)), (11/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-29362782097/2475880078570760549798248448), (15469965165/618970019642690137449562112)), (23/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (4089/1280)))⁻¹=value ((5120000/53573307), (-1744640/53573307)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/53573307), (-1744640/53573307))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39887596083/576460752303423488), (8337659899/144115188075855872)), (13/576460752303423488), by norm_num⟩
  | 1 => ⟨((-78679418547/1152921504606846976), (1229150013/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 2 => ⟨((48653159627/2305843009213693952), (-45022093445/2305843009213693952)), (13/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-6058711451/9223372036854775808), (40898829885/4611686018427387904)), (35/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-26635579979/18446744073709551616), (-1994230475/1152921504606846976)), (5/4611686018427387904), by norm_num⟩
  | 5 => ⟨((72799290233/147573952589676412928), (6292331751/147573952589676412928)), (45/147573952589676412928), by norm_num⟩
  | 6 => ⟨((-43263832025/590295810358705651712), (38131651167/590295810358705651712)), (47/590295810358705651712), by norm_num⟩
  | 7 => ⟨((1658136013/4722366482869645213696), (-83600170139/4722366482869645213696)), (43/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((41708282101/18889465931478580854784), (1194698887/590295810358705651712)), (19/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-71717632093/151115727451828646838272), (573835287/9444732965739290427392)), (127/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((2890728933/75557863725914323419136), (-37447886857/604462909807314587353088)), (105/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((9020476111/2417851639229258349412352), (96263994703/9671406556917033397649408)), (335/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-55681800377/38685626227668133590597632), (-7945256487/19342813113834066795298816)), (265/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((83/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/193078321), (-5233920/193078321)), 0, by norm_num⟩
  | 1 => ⟨((-130775841996800/37279238040179041), (88968265728000/37279238040179041)), 0, by norm_num⟩
  | 2 => ⟨((4295086565/35184372088832), (-21476697443/140737488355328)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-29771310321/9007199254740992), (75408163793/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((4615094813/144115188075855872), (-14891768071/36028797018963968)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((19334749719/4611686018427387904), (85909175359/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-8062029509/18446744073709551616), (-28156905159/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((69850069825/2361183241434822606848), (4083630929/147573952589676412928)), (1/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-63365530857/37778931862957161709568), (-30870514739/37778931862957161709568)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((102647376489/1208925819614629174706176), (4000433347/302231454903657293676544)), (15/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-9470731605/2417851639229258349412352), (5495061083/9671406556917033397649408)), (29/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((25489694469/154742504910672534362390528), (-24171202737/309485009821345068724781056)), (7/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-30663531759/4951760157141521099596496896), (14039770233/2475880078570760549798248448)), (13/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (4089/1280)))⁻¹=value ((16998400/193078321), (-5233920/193078321)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/193078321), (-5233920/193078321))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17662881849/2305843009213693952), (57965309/18014398509481984)), (25/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-29330262995/4611686018427387904), (8789733225/4611686018427387904)), (27/9223372036854775808), by norm_num⟩
  | 2 => ⟨((29191243227/18446744073709551616), (-354675115/144115188075855872)), (7/4611686018427387904), by norm_num⟩
  | 3 => ⟨((10792959699/73786976294838206464), (34250586051/36893488147419103232)), (39/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-56972827279/295147905179352825856), (-44869770473/295147905179352825856)), (45/295147905179352825856), by norm_num⟩
  | 5 => ⟨((65102200269/1180591620717411303424), (-408992881/73786976294838206464)), (51/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-4163769773/590295810358705651712), (20460304713/2361183241434822606848)), (27/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-9668567395/37778931862957161709568), (-38631193163/18889465931478580854784)), (51/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((10889389933/37778931862957161709568), (15480563951/75557863725914323419136)), (91/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-67216615771/1208925819614629174706176), (3959806861/302231454903657293676544)), (77/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((38286747491/9671406556917033397649408), (-75646391403/9671406556917033397649408)), (1/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((20504208711/38685626227668133590597632), (45382884447/38685626227668133590597632)), (103/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-109609882357/618970019642690137449562112), (-12875136803/309485009821345068724781056)), (653/618970019642690137449562112), by norm_num⟩
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
  | 0 => ⟨((91/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/228713521), (-5233920/228713521)), 0, by norm_num⟩
  | 1 => ⟨((-159968197836800/52309874688217441), (97543520256000/52309874688217441)), 0, by norm_num⟩
  | 2 => ⟨((29064636525/281474976710656), (-7808452165/70368744177664)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-1653582003/562949953421312), (51363485599/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((7843777933/144115188075855872), (-38326600309/144115188075855872)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((3806714291/4611686018427387904), (105681747197/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-24310578685/147573952589676412928), (-67498292243/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 7 => ⟨((3525598535/295147905179352825856), (39550352561/2361183241434822606848)), (11/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-12813416125/18889465931478580854784), (-5154661627/9444732965739290427392)), (5/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((81921662145/2417851639229258349412352), (17498697955/1208925819614629174706176)), (9/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-29905205359/19342813113834066795298816), (-15633044601/77371252455336267181195264)), (31/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((40420372519/618970019642690137449562112), (-5854238659/618970019642690137449562112)), (27/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-12638794219/4951760157141521099596496896), (11216171909/9903520314283042199192993792)), (3/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (4089/1280)))⁻¹=value ((18636800/228713521), (-5233920/228713521)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/228713521), (-5233920/228713521))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12872451999/18446744073709551616), (801539615/9223372036854775808)), (21/73786976294838206464), by norm_num⟩
  | 1 => ⟨((-37192655355/73786976294838206464), (45053656781/147573952589676412928)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((1654146843/18446744073709551616), (-75250626181/295147905179352825856)), (13/73786976294838206464), by norm_num⟩
  | 3 => ⟨((38283830043/1180591620717411303424), (98832625455/1180591620717411303424)), (19/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-25367669345/1180591620717411303424), (-12998468761/1180591620717411303424)), (23/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((101398400315/18889465931478580854784), (-14269660921/9444732965739290427392)), (51/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-43664455319/75557863725914323419136), (37419598309/37778931862957161709568)), (55/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-4189174873/75557863725914323419136), (-31395502579/151115727451828646838272)), (53/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((39667272123/1208925819614629174706176), (43349924067/2417851639229258349412352)), (3/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-55830871239/9671406556917033397649408), (9598568541/4835703278458516698824704)), (165/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((13774988763/38685626227668133590597632), (-16922394367/19342813113834066795298816)), (69/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((40565879899/618970019642690137449562112), (76245757363/618970019642690137449562112)), (447/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-96368365383/4951760157141521099596496896), (-17857886907/4951760157141521099596496896)), (711/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((99/8), (4089/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/29736169), (-1744640/89208507)), 0, by norm_num⟩
  | 1 => ⟨((-21316100915200/7958157721169049), (3930324992000/2652719240389683)), 0, by norm_num⟩
  | 2 => ⟨((24480983277/281474976710656), (-46339379177/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-22424679321/9007199254740992), (71491130873/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((31994010415/576460752303423488), (-12586504647/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-454631129/1152921504606846976), (16508181095/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-16253642731/295147905179352825856), (-81179864279/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 7 => ⟨((5637988257/1180591620717411303424), (46658262265/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-41936267809/151115727451828646838272), (-6187530083/18889465931478580854784)), (3/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((66322315603/4835703278458516698824704), (23439803671/2417851639229258349412352)), (19/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-47530962573/77371252455336267181195264), (-18036178865/77371252455336267181195264)), (15/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((7907315309/309485009821345068724781056), (1747424949/618970019642690137449562112)), (3/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-78866184029/79228162514264337593543950336), (11321639815/79228162514264337593543950336)), (19/39614081257132168796771975168), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (4089/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (4089/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (4089/1280)))⁻¹=value ((2252800/29736169), (-1744640/89208507)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/29736169), (-1744640/89208507))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((32210013599/590295810358705651712), (-8338967215/1180591620717411303424)), (33/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-40393009661/1180591620717411303424), (39889734909/1180591620717411303424)), (39/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((6547338369/2361183241434822606848), (-107120876183/4722366482869645213696)), (87/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((19884351451/4722366482869645213696), (62281981061/9444732965739290427392)), (33/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((-19523880821/9444732965739290427392), (-1469880671/2361183241434822606848)), (41/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((69742940801/151115727451828646838272), (-32652476535/151115727451828646838272)), (93/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-24045273391/604462909807314587353088), (59865204305/604462909807314587353088)), (25/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-37356094871/4835703278458516698824704), (-90891449479/4835703278458516698824704)), (197/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((64080405951/19342813113834066795298816), (26171752095/19342813113834066795298816)), (181/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-83134778567/154742504910672534362390528), (37821723881/154742504910672534362390528)), (315/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((4306047235/154742504910672534362390528), (-3394865037/38685626227668133590597632)), (133/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((4443078509/618970019642690137449562112), (57671838071/4951760157141521099596496896)), (433/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-76483490471/39614081257132168796771975168), (-5221072611/19807040628566084398385987584)), (691/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10740037445/1099511627776), (99230228059/2199023255552)), (483/1099511627776), by norm_num⟩
  | 1 => ⟨((-77398887111/2199023255552), (1414950021/68719476736)), (613/549755813888), by norm_num⟩
  | 2 => ⟨((-34428615201/2199023255552), (-19733555121/4398046511104)), (1471/1099511627776), by norm_num⟩
  | 3 => ⟨((-34154077899/17592186044416), (-28373611917/8796093022208)), (18833/17592186044416), by norm_num⟩
  | 4 => ⟨((1458248349/140737488355328), (-2378249521/4398046511104)), (91747/140737488355328), by norm_num⟩
  | 5 => ⟨((6425707975/1125899906842624), (-4692606849/70368744177664)), (363863/1125899906842624), by norm_num⟩
  | 6 => ⟨((27904458055/9007199254740992), (-54155248651/4503599627370496)), (1223867/9007199254740992), by norm_num⟩
  | 7 => ⟨((22211424609/18014398509481984), (-4913716509/4503599627370496)), (1795519/36028797018963968), by norm_num⟩
  | 8 => ⟨((56018865691/576460752303423488), (-17123358049/576460752303423488)), (2345527/144115188075855872), by norm_num⟩
  | 9 => ⟨((14820291215/2305843009213693952), (-14258904571/1152921504606846976)), (11088061/2305843009213693952), by norm_num⟩
  | 10 => ⟨((92518879983/36893488147419103232), (-30127069493/36893488147419103232)), (6002585/4611686018427387904), by norm_num⟩
  | 11 => ⟨((29333817735/295147905179352825856), (25565763559/147573952589676412928)), (96256655/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-60981311249/4722366482869645213696), (-31002751907/2361183241434822606848)), (90074069/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10740037445/1099511627776), (99230228059/2199023255552)), (967/2199023255552), by norm_num⟩
  | 1 => ⟨((-77398887111/2199023255552), (1414950021/68719476736)), (2453/2199023255552), by norm_num⟩
  | 2 => ⟨((-34428615201/2199023255552), (-19733555121/4398046511104)), (5885/4398046511104), by norm_num⟩
  | 3 => ⟨((-34154077899/17592186044416), (-28373611917/8796093022208)), (9417/8796093022208), by norm_num⟩
  | 4 => ⟨((1458248349/140737488355328), (-2378249521/4398046511104)), (91753/140737488355328), by norm_num⟩
  | 5 => ⟨((6425707975/1125899906842624), (-4692606849/70368744177664)), (363909/1125899906842624), by norm_num⟩
  | 6 => ⟨((27904458055/9007199254740992), (-54155248651/4503599627370496)), (306057/2251799813685248), by norm_num⟩
  | 7 => ⟨((22211424609/18014398509481984), (-4913716509/4503599627370496)), (1796961/36028797018963968), by norm_num⟩
  | 8 => ⟨((56018865691/576460752303423488), (-17123358049/576460752303423488)), (9405167/576460752303423488), by norm_num⟩
  | 9 => ⟨((14820291215/2305843009213693952), (-14258904571/1152921504606846976)), (11180295/2305843009213693952), by norm_num⟩
  | 10 => ⟨((92518879983/36893488147419103232), (-30127069493/36893488147419103232)), (12374105/9223372036854775808), by norm_num⟩
  | 11 => ⟨((29333817735/295147905179352825856), (25565763559/147573952589676412928)), (27015643/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-60981311249/4722366482869645213696), (-31002751907/2361183241434822606848)), (68648867/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile014Gamma
