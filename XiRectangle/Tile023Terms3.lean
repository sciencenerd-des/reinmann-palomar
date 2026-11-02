/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile023Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6627/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6627/640))
  have he : value ((3/4), (6627/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-311154521/134217728), (-536984639/16777216)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((736367766376835/9007199254740992), (-61743561134057/1125899906842624)), (698925/281474976710656), by norm_num⟩
  | 1 => ⟨((-2170700099/8589934592), (728042483/4294967296)), (67/8589934592), by norm_num⟩
  | 2 => ⟨((419357885/1073741824), (-2250410223/8589934592)), (105/8589934592), by norm_num⟩
  | 3 => ⟨((-3456674735/8589934592), (18114879/67108864)), (55/4294967296), by norm_num⟩
  | 4 => ⟨((333897761/1073741824), (-1791803521/8589934592)), (87/8589934592), by norm_num⟩
  | 5 => ⟨((-1651347447/8589934592), (2215416301/17179869184)), (109/17179869184), by norm_num⟩
  | 6 => ⟨((212682711/2147483648), (-2282648613/34359738368)), (57/17179869184), by norm_num⟩
  | 7 => ⟨((-3005308749/68719476736), (2015932505/68719476736)), (103/68719476736), by norm_num⟩
  | 8 => ⟨((290298029/17179869184), (-1557833239/137438953472)), (161/274877906944), by norm_num⟩
  | 9 => ⟨((-3190483669/549755813888), (2140146079/549755813888)), (113/549755813888), by norm_num⟩
  | 10 => ⟨((3944768187/2199023255552), (-2646112955/2199023255552)), (71/1099511627776), by norm_num⟩
  | 11 => ⟨((-1108495085/2199023255552), (2974271811/8796093022208)), (161/8796093022208), by norm_num⟩
  | 12 => ⟨((2284270245/17592186044416), (-3064533479/35184372088832)), (21/4398046511104), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395238986543857/2535301200456458802993406410752), (-384825428643/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111149568328903/39614081257132168796771975168), (-910475495365/633825300114114700748351602688)), (23073/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944659660436423/19807040628566084398385987584), (-1024078704375/39614081257132168796771975168)), (25959/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889068124211331/2475880078570760549798248448), (-1087826392521/2475880078570760549798248448)), (13791/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770734528992229/154742504910672534362390528), (-543768564821/77371252455336267181195264)), (27585/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549125941786383/9671406556917033397649408), (-1019258823791/9671406556917033397649408)), (12931/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629207400156557/302231454903657293676544), (-891544355485/604462909807314587353088)), (2829/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887184793493397/75557863725914323419136), (-724091995561/37778931862957161709568)), (9195/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297084284450709/4722366482869645213696), (-1085634609695/4722366482869645213696)), (6897/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620822695007841/590295810358705651712), (-1491930066963/590295810358705651712)), (9485/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455673374724259/18446744073709551616), (-1863687135951/73786976294838206464)), (5929/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455444755060445/2305843009213693952), (-1047482195997/4611686018427387904)), (13343/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593028627221503/1152921504606846976), (-2092861877315/1152921504606846976)), (26693/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193744420351111/144115188075855872), (-1828891602321/144115188075855872)), (46729/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490385357774643/36028797018963968), (-1369309642883/18014398509481984)), (17531/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487696940540993/9007199254740992), (-3415033043761/9007199254740992)), (87709/9007199254740992), by norm_num⟩
  | 2 => ⟨((556209878078637/1125899906842624), (-3402702673623/2251799813685248)), (175583/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211473047908699/2251799813685248), (-317083568927/70368744177664)), (263789/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085799805408737/1125899906842624), (-20048917055733/2251799813685248)), (529253/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1085799805408737/1125899906842624), (-20048917055733/2251799813685248)), (2018939980513762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2094077316273645/2251799813685248), (-19334853929261/1125899906842624)), (128779/281474976710656), by norm_num⟩
  | 2 => ⟨((1946738086389551/2251799813685248), (-71922341907413/2251799813685248)), (243941/281474976710656), by norm_num⟩
  | 3 => ⟨((210088410764431/281474976710656), (-31089344932565/562949953421312)), (3498955/2251799813685248), by norm_num⟩
  | 4 => ⟨((1247585245648687/2251799813685248), (-185636709732927/2251799813685248)), (2804797/1125899906842624), by norm_num⟩
  | 5 => ⟨((84488413885077/281474976710656), (-411400016477557/4503599627370496)), (14281543/4503599627370496), by norm_num⟩
  | 6 => ⟨((736367766376835/9007199254740992), (-61743561134057/1125899906842624)), (698925/281474976710656), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-311154521/134217728), (-536984639/16777216)), (1/67108864), by norm_num⟩, -5, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-157814591/67108864), (-4357655399/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((425880358146789/9007199254740992), (-372201080545681/4503599627370496)), (28271495/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1273484611/8589934592), (4451882687/17179869184)), (171/17179869184), by norm_num⟩
  | 2 => ⟨((249562727/1073741824), (-218107069/536870912)), (17/1073741824), by norm_num⟩
  | 3 => ⟨((-2086673299/8589934592), (911831271/2147483648)), (9/536870912), by norm_num⟩
  | 4 => ⟨((1635688015/8589934592), (-714760419/2147483648)), (57/4294967296), by norm_num⟩
  | 5 => ⟨((-512869031/4294967296), (3585803455/17179869184)), (145/17179869184), by norm_num⟩
  | 6 => ⟨((2144130507/34359738368), (-3747755331/34359738368)), (153/34359738368), by norm_num⟩
  | 7 => ⟨((-1920831087/68719476736), (3357447189/68719476736)), (139/68719476736), by norm_num⟩
  | 8 => ⟨((3011377381/274877906944), (-5263628121/274877906944)), (221/274877906944), by norm_num⟩
  | 9 => ⟨((-2098256969/549755813888), (916893085/137438953472)), (39/137438953472), by norm_num⟩
  | 10 => ⟨((657907259/549755813888), (-4599860743/2199023255552)), (99/1099511627776), by norm_num⟩
  | 11 => ⟨((-750132511/2199023255552), (2622333955/4398046511104)), (57/2199023255552), by norm_num⟩
  | 12 => ⟨((392006025/4398046511104), (-2740770983/17592186044416)), (121/17592186044416), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518636921/10141204801825835211973625643008), (-1369222296903/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778340759694311/633825300114114700748351602688), (-1619662627103/633825300114114700748351602688)), (23091/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236157550485995/4951760157141521099596496896), (-1821747623143/39614081257132168796771975168)), (6495/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236125683622511/309485009821345068724781056), (-1935142573489/2475880078570760549798248448)), (13803/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885335905453469/77371252455336267181195264), (-967310235365/77371252455336267181195264)), (27609/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774533538426921/4835703278458516698824704), (-1813152143385/9671406556917033397649408)), (809/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((314590806707829/151115727451828646838272), (-792976893555/302231454903657293676544)), (22655/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887100861718189/75557863725914323419136), (-644033991201/18889465931478580854784)), (36821/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648510613245729/2361183241434822606848), (-241399168339/590295810358705651712)), (13811/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810367906613289/295147905179352825856), (-82934848965/18446744073709551616)), (37989/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227823078933577/9223372036854775808), (-3315181889687/73786976294838206464)), (11875/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821656180428717/9223372036854775808), (-3726540399337/9223372036854775808)), (53457/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398226333376629/288230376151711744), (-465343114445/144115188075855872)), (26741/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193636029142829/144115188075855872), (-813284189417/36028797018963968)), (46825/144115188075855872), by norm_num⟩
  | 4 => ⟨((745110878059855/18014398509481984), (-1217796806287/9007199254740992)), (70291/36028797018963968), by norm_num⟩
  | 3 => ⟨((743745335258571/4503599627370496), (-3037052521593/4503599627370496)), (87961/9007199254740992), by norm_num⟩
  | 2 => ⟨((278052712547505/562949953421312), (-1512960294575/562949953421312)), (176213/4503599627370496), by norm_num⟩
  | 1 => ⟨((276354157721911/281474976710656), (-9022292836225/1125899906842624)), (265051/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170268431025445/2251799813685248), (-17823850898457/1125899906842624)), (133261/562949953421312), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2170268431025445/2251799813685248), (-17823850898457/1125899906842624)), (508350374461936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1045562370918739/1125899906842624), (-1073656189627/35184372088832)), (522183/1125899906842624), by norm_num⟩
  | 2 => ⟨((1939817672118533/2251799813685248), (-63810973141357/1125899906842624)), (2003431/2251799813685248), by norm_num⟩
  | 3 => ⟨((831913480301511/1125899906842624), (-219880386564393/2251799813685248)), (919703/562949953421312), by norm_num⟩
  | 4 => ⟨((1207910558435625/2251799813685248), (-324933782346239/2251799813685248)), (6154905/2251799813685248), by norm_num⟩
  | 5 => ⟨((1202119252381833/4503599627370496), (-174300994299357/1125899906842624)), (4189765/1125899906842624), by norm_num⟩
  | 6 => ⟨((425880358146789/9007199254740992), (-372201080545681/4503599627370496)), (28271495/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-157814591/67108864), (-4357655399/134217728)), (1/67108864), by norm_num⟩, -5, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-319913373/134217728), (-1104201003/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((32764553767475/4503599627370496), (-414043333400587/4503599627370496)), (32752943/9007199254740992), by norm_num⟩
  | 1 => ⟨((-397214949/17179869184), (5019577033/17179869184)), (25/2147483648), by norm_num⟩
  | 2 => ⟨((315592623/8589934592), (-124628797/268435456)), (161/8589934592), by norm_num⟩
  | 3 => ⟨((-41790431/1073741824), (4224821607/8589934592)), (43/2147483648), by norm_num⟩
  | 4 => ⟨((531248957/17179869184), (-6713355245/17179869184)), (275/17179869184), by norm_num⟩
  | 5 => ⟨((-337667557/17179869184), (2133540435/8589934592)), (177/17179869184), by norm_num⟩
  | 6 => ⟨((178854279/17179869184), (-141260549/1073741824)), (189/34359738368), by norm_num⟩
  | 7 => ⟨((-40600609/8589934592), (4104536035/68719476736)), (173/68719476736), by norm_num⟩
  | 8 => ⟨((129030921/68719476736), (-3261109117/137438953472)), (277/274877906944), by norm_num⟩
  | 9 => ⟨((-364504189/549755813888), (1151553369/137438953472)), (197/549755813888), by norm_num⟩
  | 10 => ⟨((231682787/1099511627776), (-731939719/274877906944)), (63/549755813888), by norm_num⟩
  | 11 => ⟨((-535491177/8796093022208), (3383481931/4398046511104)), (293/8796093022208), by norm_num⟩
  | 12 => ⟨((283636631/17592186044416), (-7168591807/35184372088832)), (39/4398046511104), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98804433728147/633825300114114700748351602688), (-1943272189995/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444572537835525/158456325028528675187087900672), (-1149294554495/316912650057057350374175801344)), (23107/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944601700914779/19807040628566084398385987584), (-2585374795967/39614081257132168796771975168)), (1625/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944472406947543/1237940039285380274899124224), (-1373146332623/1237940039285380274899124224)), (27629/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770611054236373/154742504910672534362390528), (-171596335835/9671406556917033397649408)), (27633/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549010009626851/9671406556917033397649408), (-160821690201/604462909807314587353088)), (25911/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258313185256539/604462909807314587353088), (-562676488367/151115727451828646838272)), (22677/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887019342332109/75557863725914323419136), (-228493879669/4722366482869645213696)), (9215/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648479955279707/2361183241434822606848), (-685154737229/1180591620717411303424)), (27653/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620651217568521/590295810358705651712), (-470778415911/73786976294838206464)), (38037/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911239229097065/36893488147419103232), (-4704600551565/73786976294838206464)), (23783/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455384036781485/2305843009213693952), (-1322075345435/2305843009213693952)), (53539/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796392283192269/576460752303423488), (-2641419206221/576460752303423488)), (26787/576460752303423488), by norm_num⟩
  | 5 => ⟨((596764767309351/72057594037927936), (-2308172202637/72057594037927936)), (11729/36028797018963968), by norm_num⟩
  | 4 => ⟨((372515093343379/9007199254740992), (-6912254768035/36028797018963968)), (17613/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487286083030727/9007199254740992), (-4309448741235/4503599627370496)), (88203/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224003998604587/4503599627370496), (-4293420196141/1125899906842624)), (88409/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105092783850089/1125899906842624), (-25600755385711/2251799813685248)), (133131/1125899906842624), by norm_num⟩
  | 0 => ⟨((542222381382991/562949953421312), (-25282778893485/1125899906842624)), (536683/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((542222381382991/562949953421312), (-25282778893485/1125899906842624)), (2047283181197356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((521974119297215/562949953421312), (-48703755977915/1125899906842624)), (1057949/2251799813685248), by norm_num⟩
  | 2 => ⟨((241463708809521/281474976710656), (-180634885772965/2251799813685248)), (256677/281474976710656), by norm_num⟩
  | 3 => ⟨((1642629716271019/2251799813685248), (-154957893482519/1125899906842624)), (3852495/2251799813685248), by norm_num⟩
  | 4 => ⟨((72225131147087/140737488355328), (-56518887482403/281474976710656)), (835129/281474976710656), by norm_num⟩
  | 5 => ⟨((251127028642019/1125899906842624), (-116019807043813/562949953421312)), (9540325/2251799813685248), by norm_num⟩
  | 6 => ⟨((32764553767475/4503599627370496), (-414043333400587/4503599627370496)), (32752943/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-319913373/134217728), (-1104201003/33554432)), (1/67108864), by norm_num⟩, -5, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-162011325/67108864), (-4473537711/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-542996149546395/18014398509481984), (-1517004815006971/18014398509481984)), (17662433/9007199254740992), by norm_num⟩
  | 1 => ⟨((1666867427/17179869184), (2328419745/8589934592)), (55/8589934592), by norm_num⟩
  | 2 => ⟨((-167669977/1073741824), (-1873723507/4294967296)), (45/4294967296), by norm_num⟩
  | 3 => ⟨((1439223561/8589934592), (4020855533/8589934592)), (49/4294967296), by norm_num⟩
  | 4 => ⟨((-579085241/4294967296), (-808914667/2147483648)), (81/8589934592), by norm_num⟩
  | 5 => ⟨((745601393/8589934592), (2083036693/8589934592)), (53/8589934592), by norm_num⟩
  | 6 => ⟨((-799999433/17179869184), (-2235012151/17179869184)), (29/8589934592), by norm_num⟩
  | 7 => ⟨((183935631/8589934592), (2055493309/34359738368)), (109/68719476736), by norm_num⟩
  | 8 => ⟨((-148016489/17179869184), (-827047215/34359738368)), (89/137438953472), by norm_num⟩
  | 9 => ⟨((26469261/8589934592), (2366366477/274877906944)), (65/274877906944), by norm_num⟩
  | 10 => ⟨((-2181152367/2199023255552), (-6093631877/2199023255552)), (169/2199023255552), by norm_num⟩
  | 11 => ⟨((638259875/2199023255552), (1783149485/2199023255552)), (25/1099511627776), by norm_num⟩
  | 12 => ⟨((-684826427/8796093022208), (-956622795/4398046511104)), (109/17592186044416), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98801941140089/633825300114114700748351602688), (-2493884828125/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889120573700273/316912650057057350374175801344), (-2949729192015/633825300114114700748351602688)), (5781/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944574091074591/19807040628566084398385987584), (-829435816879/9903520314283042199192993792)), (6505/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944443011214947/1237940039285380274899124224), (-3524233540199/2475880078570760549798248448)), (13825/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885276063646577/77371252455336267181195264), (-3523256575647/154742504910672534362390528)), (3457/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548954621787327/9671406556917033397649408), (-3302015318667/9671406556917033397649408)), (12967/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629132288598143/302231454903657293676544), (-2888226024507/604462909807314587353088)), (5675/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117933755316915/4722366482869645213696), (-4691422929477/75557863725914323419136)), (18449/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648450116185099/2361183241434822606848), (-3516866607505/4722366482869645213696)), (6921/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620568778303489/590295810358705651712), (-2416464743749/295147905179352825856)), (9521/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911187418690655/36893488147419103232), (-6037021092325/73786976294838206464)), (23815/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910709394521411/4611686018427387904), (-6785959039639/9223372036854775808)), (26809/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796333114828013/576460752303423488), (-3389426361819/576460752303423488)), (26831/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298356223003153/36028797018963968), (-370219343263/9007199254740992)), (23503/144115188075855872), by norm_num⟩
  | 4 => ⟨((372475305258059/9007199254740992), (-8869310854677/36028797018963968)), (4413/4503599627370496), by norm_num⟩
  | 3 => ⟨((371770832424393/2251799813685248), (-11058764882413/9007199254740992)), (22109/4503599627370496), by norm_num⟩
  | 2 => ⟨((555896780108325/1125899906842624), (-11017043734865/2251799813685248)), (22175/1125899906842624), by norm_num⟩
  | 1 => ⟨((2209532056105263/2251799813685248), (-32843150330007/2251799813685248)), (133713/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083735562467989/1125899906842624), (-32429059941365/1125899906842624)), (67523/562949953421312), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1083735562467989/1125899906842624), (-32429059941365/1125899906842624)), (257579805614280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((521108101305291/562949953421312), (-124858436535161/2251799813685248)), (267757/1125899906842624), by norm_num⟩
  | 2 => ⟨((480645392682231/562949953421312), (-231156401734669/2251799813685248)), (525405/1125899906842624), by norm_num⟩
  | 3 => ⟨((808883319001991/1125899906842624), (-394721622437443/2251799813685248)), (2010099/2251799813685248), by norm_num⟩
  | 4 => ⟨((273266269148371/562949953421312), (-283580924111115/1125899906842624)), (1796475/1125899906842624), by norm_num⟩
  | 5 => ⟨((387742593405999/2251799813685248), (-1101243201638507/4503599627370496)), (10596169/4503599627370496), by norm_num⟩
  | 6 => ⟨((-542996149546395/18014398509481984), (-1517004815006971/18014398509481984)), (17662433/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/67108864), (-4473537711/134217728)), (1/134217728), by norm_num⟩, -5, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-20498171/8388608), (-4528045977/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-133285673865175/2251799813685248), (-1144926044132373/18014398509481984)), (4470239/1125899906842624), by norm_num⟩
  | 1 => ⟨((1656561251/8589934592), (3557471829/17179869184)), (7/536870912), by norm_num⟩
  | 2 => ⟨((-1349309119/4294967296), (-2897646663/8589934592)), (185/8589934592), by norm_num⟩
  | 3 => ⟨((1465393123/4294967296), (196683595/536870912)), (203/8589934592), by norm_num⟩
  | 4 => ⟨((-1193598065/4294967296), (-160203535/536870912)), (167/8589934592), by norm_num⟩
  | 5 => ⟨((3111086179/17179869184), (1670267465/8589934592)), (55/4294967296), by norm_num⟩
  | 6 => ⟨((-3378739703/34359738368), (-1813964215/17179869184)), (241/34359738368), by norm_num⟩
  | 7 => ⟨((786304295/17179869184), (3377183159/68719476736)), (113/34359738368), by norm_num⟩
  | 8 => ⟨((-2561855301/137438953472), (-1375398595/68719476736)), (93/68719476736), by norm_num⟩
  | 9 => ⟨((1854838197/274877906944), (995818089/137438953472)), (271/549755813888), by norm_num⟩
  | 10 => ⟨((-2417296763/1099511627776), (-2595577175/1099511627776)), (89/549755813888), by norm_num⟩
  | 11 => ⟨((715980565/1099511627776), (3075142185/4398046511104)), (213/4398046511104), by norm_num⟩
  | 12 => ⟨((-3110311733/17592186044416), (-3339703369/17592186044416)), (233/17592186044416), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395198185306375/2535301200456458802993406410752), (-1511449582387/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778193639759707/633825300114114700748351602688), (-3575265662519/633825300114114700748351602688)), (23139/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889094626085165/39614081257132168796771975168), (-7854117759/77371252455336267181195264)), (26037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944414486042523/1237940039285380274899124224), (-1067893449561/618970019642690137449562112)), (27671/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770494911717699/154742504910672534362390528), (-4270374549709/154742504910672534362390528)), (13839/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548900806769439/9671406556917033397649408), (-4002202273721/9671406556917033397649408)), (6489/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629108656899529/302231454903657293676544), (-3500653499351/604462909807314587353088)), (355/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((943431476891213/37778931862957161709568), (-710771867795/9444732965739290427392)), (18467/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81052631062995/295147905179352825856), (-266408961677/295147905179352825856)), (27713/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620488376607695/590295810358705651712), (-5857605949141/590295810358705651712)), (19063/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822273638010297/73786976294838206464), (-7316923248885/73786976294838206464)), (5961/9223372036854775808), by norm_num⟩
  | 7 => ⟨((227662997853525/1152921504606846976), (-4112276080365/4611686018427387904)), (53693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796275114991443/576460752303423488), (-8215825437343/1152921504606846976)), (53747/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193322053357331/144115188075855872), (-7179038484665/144115188075855872)), (23545/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489744294400415/36028797018963968), (-10748962153249/36028797018963968)), (17689/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486882522006159/9007199254740992), (-13401959862005/9007199254740992)), (44329/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111585819786257/2251799813685248), (-26701388867185/4503599627370496)), (177957/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104437229862425/1125899906842624), (-39796447568825/2251799813685248)), (1049/8796093022208), by norm_num⟩
  | 0 => ⟨((541505038988359/562949953421312), (-2455453069519/70368744177664)), (543551/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((541505038988359/562949953421312), (-2455453069519/70368744177664)), (2073482522017668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((32511974808367/35184372088832), (-151162590798773/2251799813685248)), (135453/281474976710656), by norm_num⟩
  | 2 => ⟨((1912576155881493/2251799813685248), (-34920293103491/281474976710656)), (537031/562949953421312), by norm_num⟩
  | 3 => ⟨((1589796841878175/2251799813685248), (-474555292457025/2251799813685248)), (2091019/1125899906842624), by norm_num⟩
  | 4 => ⟨((1022404948634857/2251799813685248), (-335041552388283/1125899906842624)), (3833911/1125899906842624), by norm_num⟩
  | 5 => ⟨((529621246135685/4503599627370496), (-76060966671695/281474976710656)), (11526511/2251799813685248), by norm_num⟩
  | 6 => ⟨((-133285673865175/2251799813685248), (-1144926044132373/18014398509481984)), (4470239/1125899906842624), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20498171/8388608), (-4528045977/134217728)), (1/67108864), by norm_num⟩, -5, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-165884901/67108864), (-4580496829/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-345583434245917/4503599627370496), (-634232334146629/18014398509481984)), (34082909/18014398509481984), by norm_num⟩
  | 1 => ⟨((1086222289/4294967296), (1993490513/17179869184)), (109/17179869184), by norm_num⟩
  | 2 => ⟨((-3580011465/8589934592), (-1642554881/8589934592)), (23/2147483648), by norm_num⟩
  | 3 => ⟨((3933044589/8589934592), (1804530977/8589934592)), (103/8589934592), by norm_num⟩
  | 4 => ⟨((-1620334169/4294967296), (-743429965/4294967296)), (43/4294967296), by norm_num⟩
  | 5 => ⟨((4272285671/17179869184), (1960179109/17179869184)), (115/17179869184), by norm_num⟩
  | 6 => ⟨((-4693585539/34359738368), (-2153476857/34359738368)), (1/268435456), by norm_num⟩
  | 7 => ⟨((2209898893/34359738368), (2027859547/68719476736)), (123/68719476736), by norm_num⟩
  | 8 => ⟨((-3641733121/137438953472), (-1670873563/137438953472)), (103/137438953472), by norm_num⟩
  | 9 => ⟨((5334470345/549755813888), (611880743/137438953472)), (153/549755813888), by norm_num⟩
  | 10 => ⟨((-3516308805/1099511627776), (-201665911/137438953472)), (103/1099511627776), by norm_num⟩
  | 11 => ⟨((2107123671/2199023255552), (1933550383/4398046511104)), (125/4398046511104), by norm_num⟩
  | 12 => ⟨((-4629823917/17592186044416), (-2124222211/17592186044416)), (35/4398046511104), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (-3531945860141/10141204801825835211973625643008)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778147531211857/633825300114114700748351602688), (-4177133876827/633825300114114700748351602688)), (5789/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118065164170733/2475880078570760549798248448), (-1174561712909/9903520314283042199192993792)), (3257/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888773552443035/2475880078570760549798248448), (-4990626377049/2475880078570760549798248448)), (6923/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770439300653285/154742504910672534362390528), (-4989208111757/154742504910672534362390528)), (6925/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548848468176249/9671406556917033397649408), (-4675876042465/9671406556917033397649408)), (12989/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258171314496383/604462909807314587353088), (-4089885361899/604462909807314587353088)), (5685/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235848478077997/9444732965739290427392), (-1660810114273/18889465931478580854784)), (4621/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648392708890077/2361183241434822606848), (-1244990204147/1180591620717411303424)), (13871/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810204951664337/295147905179352825856), (-6843434685681/590295810358705651712)), (4771/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911087369349241/36893488147419103232), (-4274139451141/36893488147419103232)), (11937/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455297903151177/2305843009213693952), (-9608548279779/9223372036854775808)), (26883/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796218238647783/576460752303423488), (-4799111505171/576460752303423488)), (26915/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596610484410707/72057594037927936), (-8386838266589/144115188075855872)), (11793/72057594037927936), by norm_num⟩
  | 4 => ⟨((744794788277335/18014398509481984), (-6278533163203/18014398509481984)), (17725/18014398509481984), by norm_num⟩
  | 3 => ⟨((743341869846297/4503599627370496), (-15655799544411/9007199254740992)), (44437/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111379008486359/2251799813685248), (-15595101595145/2251799813685248)), (44625/2251799813685248), by norm_num⟩
  | 1 => ⟨((552053554890407/562949953421312), (-23241265149863/1125899906842624)), (67407/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082271237313379/1125899906842624), (-45879129423187/1125899906842624)), (136701/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1082271237313379/1125899906842624), (-45879129423187/1125899906842624)), (521472935203170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1038463658708369/1125899906842624), (-88202622392851/1125899906842624)), (136975/562949953421312), by norm_num⟩
  | 2 => ⟨((475453928610479/562949953421312), (-162705791875611/1125899906842624)), (1096547/2251799813685248), by norm_num⟩
  | 3 => ⟨((779600897806429/1125899906842624), (-549669522022627/2251799813685248)), (2169163/2251799813685248), by norm_num⟩
  | 4 => ⟨((236363557171357/562949953421312), (-761209500527241/2251799813685248)), (4062961/2251799813685248), by norm_num⟩
  | 5 => ⟨((279282192791031/4503599627370496), (-1278424017650441/4503599627370496)), (3079363/1125899906842624), by norm_num⟩
  | 6 => ⟨((-345583434245917/4503599627370496), (-634232334146629/18014398509481984)), (34082909/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-4580496829/134217728)), (1/134217728), by norm_num⟩, -5, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile023Terms3
