/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile017Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/128))
  have he : value ((3/4), (987/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2489236171/1073741824), (-25592459387/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((477955101930137/18014398509481984), (853880742818995/9007199254740992)), (8143033/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1408938895/17179869184), (-629277617/2147483648)), (49/34359738368), by norm_num⟩
  | 2 => ⟨((4355089939/34359738368), (15560990633/34359738368)), (39/17179869184), by norm_num⟩
  | 3 => ⟨((-4487255963/34359738368), (-8016613777/17179869184)), (41/17179869184), by norm_num⟩
  | 4 => ⟨((1733787335/17179869184), (6194923379/17179869184)), (129/68719476736), by norm_num⟩
  | 5 => ⟨((-2143684103/34359738368), (-478719279/2147483648)), (81/68719476736), by norm_num⟩
  | 6 => ⟨((2208739523/68719476736), (3945977639/34359738368)), (85/137438953472), by norm_num⟩
  | 7 => ⟨((-487664831/34359738368), (-13939639317/274877906944)), (77/274877906944), by norm_num⟩
  | 8 => ⟨((3014785391/549755813888), (2693001057/137438953472)), (121/1099511627776), by norm_num⟩
  | 9 => ⟨((-2070851029/1099511627776), (-7399271639/1099511627776)), (85/2199023255552), by norm_num⟩
  | 10 => ⟨((1280217689/2199023255552), (571786569/274877906944)), (107/8796093022208), by norm_num⟩
  | 11 => ⟨((-719492223/4398046511104), (-10283150889/17592186044416)), (123/35184372088832), by norm_num⟩
  | 12 => ⟨((370663501/8796093022208), (21190437301/140737488355328)), (129/140737488355328), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395238986542947/2535301200456458802993406410752), (1690667557297/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778391394451669/633825300114114700748351602688), (2000012560433/633825300114114700748351602688)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472329328768335/9903520314283042199192993792), (2249558962981/39614081257132168796771975168)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889065868359369/2475880078570760549798248448), (597397774407/618970019642690137449562112)), (3453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770732133000221/154742504910672534362390528), (1194477683497/77371252455336267181195264)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774561773375421/4835703278458516698824704), (559742601851/2417851639229258349412352)), (1619/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629206277991525/302231454903657293676544), (979212049403/302231454903657293676544)), (1417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943590433973103/37778931862957161709568), (1590587017067/37778931862957161709568)), (2303/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297081096845995/4722366482869645213696), (298096756591/590295810358705651712)), (27/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1620817916927677/590295810358705651712), (3277267265045/590295810358705651712)), (4753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822686934438841/73786976294838206464), (4093890175915/73786976294838206464)), (5943/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821770822764817/9223372036854775808), (4601925057611/9223372036854775808)), (6689/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593019416179901/1152921504606846976), (4597302411253/1152921504606846976)), (1673/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193735223192035/144115188075855872), (1004361188445/36028797018963968)), (1465/36028797018963968), by norm_num⟩
  | 4 => ⟨((745184646967119/18014398509481984), (375986966065/2251799813685248)), (8799/36028797018963968), by norm_num⟩
  | 3 => ⟨((743836453518861/4503599627370496), (7501613440025/9007199254740992)), (11013/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224779645925801/4503599627370496), (14948975231475/4503599627370496)), (11035/2251799813685248), by norm_num⟩
  | 1 => ⟨((2211353965124045/2251799813685248), (22288273832339/2251799813685248)), (33217/2251799813685248), by norm_num⟩
  | 0 => ⟨((2171245597685411/2251799813685248), (22019212620179/1125899906842624)), (66885/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2171245597685411/2251799813685248), (22019212620179/1125899906842624)), (255146035201262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((523177952357415/562949953421312), (84926054572887/2251799813685248)), (65801/1125899906842624), by norm_num⟩
  | 2 => ⟨((485415072868483/562949953421312), (78926091143993/1125899906842624)), (31817/281474976710656), by norm_num⟩
  | 3 => ⟨((415792664302645/562949953421312), (272222523874787/2251799813685248)), (474645/2251799813685248), by norm_num⟩
  | 4 => ⟨((597751078080025/1125899906842624), (402125012346801/2251799813685248)), (25497/70368744177664), by norm_num⟩
  | 5 => ⟨((1125784691982913/4503599627370496), (426984065266189/2251799813685248)), (2315501/4503599627370496), by norm_num⟩
  | 6 => ⟨((477955101930137/18014398509481984), (853880742818995/9007199254740992)), (8143033/18014398509481984), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2489236171/1073741824), (-25592459387/1073741824)), (1/536870912), by norm_num⟩, -4, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2525033459/1073741824), (-25960500249/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((495268748084701/9007199254740992), (700155354156033/9007199254740992)), (3366489/9007199254740992), by norm_num⟩
  | 1 => ⟨((-5923890285/34359738368), (-8374531033/34359738368)), (83/68719476736), by norm_num⟩
  | 2 => ⟨((4643580931/17179869184), (13129146807/34359738368)), (67/34359738368), by norm_num⟩
  | 3 => ⟨((-2426653525/8589934592), (-13722121291/34359738368)), (9/4294967296), by norm_num⟩
  | 4 => ⟨((1902189523/8589934592), (672275499/2147483648)), (29/17179869184), by norm_num⟩
  | 5 => ⟨((-9542886795/68719476736), (-13490662007/68719476736)), (37/34359738368), by norm_num⟩
  | 6 => ⟨((9973888783/137438953472), (7049982115/68719476736)), (79/137438953472), by norm_num⟩
  | 7 => ⟨((-8935163025/274877906944), (-98683831/2147483648)), (73/274877906944), by norm_num⟩
  | 8 => ⟨((14008075991/1099511627776), (19803045203/1099511627776)), (117/1099511627776), by norm_num⟩
  | 9 => ⟨((-9760498055/2199023255552), (-1724787047/274877906944)), (21/549755813888), by norm_num⟩
  | 10 => ⟨((6120797039/4398046511104), (8652895695/4398046511104)), (27/2199023255552), by norm_num⟩
  | 11 => ⟨((-13957617245/35184372088832), (-19731712293/35184372088832)), (63/17592186044416), by norm_num⟩
  | 12 => ⟨((3647002345/35184372088832), (10311444961/70368744177664)), (67/70368744177664), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316641/5070602400912917605986812821504), (622089091697/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55573156396355/19807040628566084398385987584), (91984191941/39614081257132168796771975168)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889260693124841/39614081257132168796771975168), (206922112499/4951760157141521099596496896)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889005794273671/2475880078570760549798248448), (1758416106583/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885336078203653/77371252455336267181195264), (878970859177/77371252455336267181195264)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774533711107339/4835703278458516698824704), (1647566494771/9671406556917033397649408)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258363550458873/604462909807314587353088), (1441117009501/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943550713885017/37778931862957161709568), (2340871162211/75557863725914323419136)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297021686130821/4722366482869645213696), (1754827799957/4722366482869645213696)), (3453/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620736502199753/590295810358705651712), (1205773718925/295147905179352825856)), (4749/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822585578017629/73786976294838206464), (753106114491/18446744073709551616)), (5937/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910828681216079/4611686018427387904), (3386216164145/9223372036854775808)), (6681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592906661635425/1152921504606846976), (3382767739655/1152921504606846976)), (1671/288230376151711744), by norm_num⟩
  | 5 => ⟨((298409338810693/36028797018963968), (739011694675/36028797018963968)), (5851/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490224072235815/36028797018963968), (4426331377963/36028797018963968)), (8783/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487494135590093/9007199254740992), (2759698248255/4503599627370496)), (10989/9007199254740992), by norm_num⟩
  | 2 => ⟨((556107582820857/1125899906842624), (10998340260595/4503599627370496)), (22011/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210850428550235/2251799813685248), (16396729303679/2251799813685248)), (33099/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170319458345459/2251799813685248), (16196216107229/1125899906842624)), (66533/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2170319458345459/2251799813685248), (16196216107229/1125899906842624)), (253803261763762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((65353795730807/70368744177664), (62440653481643/2251799813685248)), (65083/1125899906842624), by norm_num⟩
  | 2 => ⟨((485137111373547/562949953421312), (14497678481495/281474976710656)), (248999/2251799813685248), by norm_num⟩
  | 3 => ⟨((1666345540531169/2251799813685248), (24987520888455/281474976710656)), (227407/1125899906842624), by norm_num⟩
  | 4 => ⟨((607679991579613/1125899906842624), (73963668969779/562949953421312)), (376941/1125899906842624), by norm_num⟩
  | 5 => ⟨((1234185997334387/4503599627370496), (159681127828835/1125899906842624)), (505941/1125899906842624), by norm_num⟩
  | 6 => ⟨((495268748084701/9007199254740992), (700155354156033/9007199254740992)), (3366489/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2525033459/1073741824), (-25960500249/1073741824)), (1/536870912), by norm_num⟩, -4, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2559306987/1073741824), (-26312874965/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((672689894070009/9007199254740992), (487349868398945/9007199254740992)), (2686119/9007199254740992), by norm_num⟩
  | 1 => ⟨((-16310460621/68719476736), (-11816590241/68719476736)), (67/68719476736), by norm_num⟩
  | 2 => ⟨((12958880463/34359738368), (9388439969/34359738368)), (55/34359738368), by norm_num⟩
  | 3 => ⟨((-3432001641/8589934592), (-2486413967/8589934592)), (15/8589934592), by norm_num⟩
  | 4 => ⟨((10907085961/34359738368), (987744679/4294967296)), (49/34359738368), by norm_num⟩
  | 5 => ⟨((-13865322527/68719476736), (-5022569217/34359738368)), (1/1073741824), by norm_num⟩
  | 6 => ⟨((7344123561/68719476736), (5320665113/68719476736)), (35/68719476736), by norm_num⟩
  | 7 => ⟨((-6668577147/137438953472), (-4831245755/137438953472)), (65/274877906944), by norm_num⟩
  | 8 => ⟨((10596548573/549755813888), (7676979539/549755813888)), (53/549755813888), by norm_num⟩
  | 9 => ⟨((-14967289681/2199023255552), (-10843490769/2199023255552)), (77/2199023255552), by norm_num⟩
  | 10 => ⟨((19026740921/8796093022208), (13784478949/8796093022208)), (25/2199023255552), by norm_num⟩
  | 11 => ⟨((-5497091533/8796093022208), (-7965057477/17592186044416)), (59/17592186044416), by norm_num⟩
  | 12 => ⟨((2911675467/17592186044416), (527362113/4398046511104)), (1/1099511627776), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197608867455839/1267650600228229401496703205376), (51043388759/633825300114114700748351602688)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778292482379997/633825300114114700748351602688), (966022387113/633825300114114700748351602688)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472301538414899/9903520314283042199192993792), (33954704035/1237940039285380274899124224)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944473954378391/1237940039285380274899124224), (1154179340277/2475880078570760549798248448)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770614341327653/154742504910672534362390528), (576931903061/77371252455336267181195264)), (3449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549013295369669/9671406556917033397649408), (1081412182531/9671406556917033397649408)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258316264208293/604462909807314587353088), (945900658297/604462909807314587353088)), (1415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887024727634775/75557863725914323419136), (768230363655/37778931862957161709568)), (4599/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296964283435329/4722366482869645213696), (1151796468449/4722366482869645213696)), (1725/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810328886095491/295147905179352825856), (1582828428161/590295810358705651712)), (593/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455621865795517/18446744073709551616), (1977198895523/73786976294838206464)), (5931/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113846711996487/576460752303423488), (1111256197447/4611686018427387904)), (6673/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592797201122221/1152921504606846976), (555054803773/288230376151711744)), (6675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193542149777571/144115188075855872), (970057554257/72057594037927936)), (5843/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490082405915877/36028797018963968), (2905027049793/36028797018963968)), (137/562949953421312), by norm_num⟩
  | 3 => ⟨((1487319044039859/9007199254740992), (3622296503813/9007199254740992)), (10967/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224086094563397/4503599627370496), (7217701001585/4503599627370496)), (21955/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210348842929817/2251799813685248), (10759565585241/2251799813685248)), (32987/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169374788775533/2251799813685248), (10626323573329/1125899906842624)), (66195/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2169374788775533/2251799813685248), (10626323573329/1125899906842624)), (252513894087981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089766270769355/2251799813685248), (40949427772843/2251799813685248)), (128795/2251799813685248), by norm_num⟩
  | 2 => ⟨((1938647558401711/2251799813685248), (19001407773221/562949953421312)), (60935/562949953421312), by norm_num⟩
  | 3 => ⟨((1666479176760255/2251799813685248), (130871430264357/2251799813685248)), (218071/1125899906842624), by norm_num⟩
  | 4 => ⟨((612848775131369/1125899906842624), (96853420114399/1125899906842624)), (174061/562949953421312), by norm_num⟩
  | 5 => ⟨((325253633974543/1125899906842624), (421753298130009/4503599627370496)), (1755489/4503599627370496), by norm_num⟩
  | 6 => ⟨((672689894070009/9007199254740992), (487349868398945/9007199254740992)), (2686119/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2559306987/1073741824), (-26312874965/1073741824)), (1/536870912), by norm_num⟩, -4, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-162011325/67108864), (-13325431479/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((1533373344583253/18014398509481984), (1933158147343/70368744177664)), (4134003/18014398509481984), by norm_num⟩
  | 1 => ⟨((-9414173869/34359738368), (-1519188483/17179869184)), (53/68719476736), by norm_num⟩
  | 2 => ⟨((15151528339/34359738368), (4890079081/34359738368)), (11/8589934592), by norm_num⟩
  | 3 => ⟨((-2032120345/4294967296), (-5246852445/34359738368)), (49/34359738368), by norm_num⟩
  | 4 => ⟨((13082286103/34359738368), (4222241623/34359738368)), (41/34359738368), by norm_num⟩
  | 5 => ⟨((-4211025447/17179869184), (-5436348595/68719476736)), (55/68719476736), by norm_num⟩
  | 6 => ⟨((4518256003/34359738368), (5832977023/137438953472)), (61/137438953472), by norm_num⟩
  | 7 => ⟨((-4155344291/68719476736), (-2682232675/137438953472)), (29/137438953472), by norm_num⟩
  | 8 => ⟨((6687768641/274877906944), (4316886957/549755813888)), (3/34359738368), by norm_num⟩
  | 9 => ⟨((-4783799289/549755813888), (-6175788029/2199023255552)), (35/1099511627776), by norm_num⟩
  | 10 => ⟨((24637529411/8796093022208), (3975818957/4398046511104)), (93/8796093022208), by norm_num⟩
  | 11 => ⟨((-14419117783/17592186044416), (-2326848641/8796093022208)), (7/2199023255552), by norm_num⟩
  | 12 => ⟨((15471116549/70368744177664), (4993224559/70368744177664)), (61/70368744177664), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98801941140089/633825300114114700748351602688), (406663533439/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444561421530925/158456325028528675187087900672), (480995466345/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889153539781785/39614081257132168796771975168), (270503400133/19807040628566084398385987584)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944446023947663/1237940039285380274899124224), (17958694821/77371252455336267181195264)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885279263492075/77371252455336267181195264), (574519129275/154742504910672534362390528)), (3447/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774480509408989/4835703278458516698824704), (538442696653/9671406556917033397649408)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258270571587149/604462909807314587353088), (470968442327/604462909807314587353088)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886950569606701/75557863725914323419136), (765007147195/75557863725914323419136)), (4595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648454372881883/2361183241434822606848), (71684813553/590295810358705651712)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405145384784703/147573952589676412928), (788083342267/590295810358705651712)), (1185/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822392368501583/73786976294838206464), (492215126567/36893488147419103232)), (1481/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821440680420179/9223372036854775808), (553279088321/4611686018427387904)), (3333/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592690826518047/1152921504606846976), (552701017671/576460752303423488)), (6667/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193449450250103/144115188075855872), (482963872253/72057594037927936)), (5835/144115188075855872), by norm_num⟩
  | 4 => ⟨((186243013896591/4503599627370496), (361574398699/9007199254740992)), (4377/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487147491682841/9007199254740992), (1803341554441/9007199254740992)), (5473/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111873460283223/2251799813685248), (3593128113981/4503599627370496)), (21901/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209849847706303/2251799813685248), (2677965736797/1125899906842624)), (2055/140737488355328), by norm_num⟩
  | 0 => ⟨((1084207748541001/1125899906842624), (5288789099829/1125899906842624)), (65873/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1084207748541001/1125899906842624), (5288789099829/1125899906842624)), (251285561568450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((261008652625839/281474976710656), (20371779365411/2251799813685248)), (249/4398046511104), by norm_num⟩
  | 2 => ⟨((968029670272111/1125899906842624), (18890527129247/1125899906842624)), (29843/281474976710656), by norm_num⟩
  | 3 => ⟨((207994641623779/281474976710656), (32483510544863/1125899906842624)), (104637/562949953421312), by norm_num⟩
  | 4 => ⟨((1227699109751423/2251799813685248), (48007081932589/1125899906842624)), (20085/70368744177664), by norm_num⟩
  | 5 => ⟨((332628676696191/1125899906842624), (209390733198245/4503599627370496)), (1511285/4503599627370496), by norm_num⟩
  | 6 => ⟨((1533373344583253/18014398509481984), (1933158147343/70368744177664)), (4134003/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/67108864), (-13325431479/536870912)), (1/536870912), by norm_num⟩, -4, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1311882945/536870912), (-26975593053/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((391119138573285/4503599627370496), (7636808449851/9007199254740992)), (3058069/18014398509481984), by norm_num⟩
  | 1 => ⟨((-19444334585/68719476736), (-189830469/68719476736)), (5/8589934592), by norm_num⟩
  | 2 => ⟨((15837879799/34359738368), (309242997/68719476736)), (67/68719476736), by norm_num⟩
  | 3 => ⟨((-8600223557/17179869184), (-167923923/34359738368)), (19/17179869184), by norm_num⟩
  | 4 => ⟨((28020358597/68719476736), (17097261/4294967296)), (1/1073741824), by norm_num⟩
  | 5 => ⟨((-4564651667/17179869184), (-89127243/34359738368)), (43/68719476736), by norm_num⟩
  | 6 => ⟨((19829434391/137438953472), (48397527/34359738368)), (3/8589934592), by norm_num⟩
  | 7 => ⟨((-18458917583/274877906944), (-90105037/137438953472)), (23/137438953472), by norm_num⟩
  | 8 => ⟨((3758808467/137438953472), (293570909/1099511627776)), (77/1099511627776), by norm_num⟩
  | 9 => ⟨((-21771663739/2199023255552), (-53137909/549755813888)), (57/2199023255552), by norm_num⟩
  | 10 => ⟨((14186836451/4398046511104), (69251375/2199023255552)), (19/2199023255552), by norm_num⟩
  | 11 => ⟨((-33616060165/35184372088832), (-328185695/35184372088832)), (23/8796093022208), by norm_num⟩
  | 12 => ⟨((18254061541/70368744177664), (178210113/70368744177664)), (51/70368744177664), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396370611537/5070602400912917605986812821504), (12716687385/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889100245147741/316912650057057350374175801344), (7520187289/316912650057057350374175801344)), (1441/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889102712054233/39614081257132168796771975168), (16916845411/39614081257132168796771975168)), (1621/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888838065934179/2475880078570760549798248448), (4492417563/618970019642690137449562112)), (3445/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110656535644819/9671406556917033397649408), (4491158713/38685626227668133590597632)), (3445/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548910461303641/9671406556917033397649408), (16836497059/9671406556917033397649408)), (1615/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258226360607399/604462909807314587353088), (3681647265/151115727451828646838272)), (1413/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471719694266537/18889465931478580854784), (11960344249/37778931862957161709568)), (287/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648427472669417/2361183241434822606848), (17931754761/4722366482869645213696)), (3445/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810253817480153/295147905179352825856), (3080241765/73786976294838206464)), (4735/590295810358705651712), by norm_num⟩
  | 8 => ⟨((7118359747179/288230376151711744), (30781090273/73786976294838206464)), (5919/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910668509995091/4611686018427387904), (34599426805/9223372036854775808)), (6659/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796293674752843/576460752303423488), (34562840163/1152921504606846976)), (6659/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193359113844219/144115188075855872), (30201377427/144115188075855872)), (5827/144115188075855872), by norm_num⟩
  | 4 => ⟨((93113063600819/2251799813685248), (45219981169/36028797018963968)), (2185/9007199254740992), by norm_num⟩
  | 3 => ⟨((743489671012419/4503599627370496), (28190810401/4503599627370496)), (10925/9007199254740992), by norm_num⟩
  | 2 => ⟨((34740824452637/70368744177664), (112334344301/4503599627370496)), (10925/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104676972578821/1125899906842624), (167433355923/2251799813685248)), (4097/281474976710656), by norm_num⟩
  | 0 => ⟨((541861211369305/562949953421312), (165309238599/1125899906842624)), (65563/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((541861211369305/562949953421312), (165309238599/1125899906842624)), (250103005416106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2086249861256025/2251799813685248), (636466270107/2251799813685248)), (63117/1125899906842624), by norm_num⟩
  | 2 => ⟨((1932870787203043/2251799813685248), (73709242471/140737488355328)), (233979/2251799813685248), by norm_num⟩
  | 3 => ⟨((1659111998524971/2251799813685248), (1012313372819/1125899906842624)), (200963/1125899906842624), by norm_num⟩
  | 4 => ⟨((1222421508256161/2251799813685248), (2983464609783/2251799813685248)), (592997/2251799813685248), by norm_num⟩
  | 5 => ⟨((663604923361567/2251799813685248), (3239232267411/2251799813685248)), (1290811/4503599627370496), by norm_num⟩
  | 6 => ⟨((391119138573285/4503599627370496), (7636808449851/9007199254740992)), (3058069/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1311882945/536870912), (-26975593053/1073741824)), (1/536870912), by norm_num⟩, -4, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-165884901/67108864), (-27288066215/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((1461129820953947/18014398509481984), (-824479882173/35184372088832)), (951849/4503599627370496), by norm_num⟩
  | 1 => ⟨((-18370229835/68719476736), (5307326545/68719476736)), (25/34359738368), by norm_num⟩
  | 2 => ⟨((7568160091/17179869184), (-2186510311/17179869184)), (43/34359738368), by norm_num⟩
  | 3 => ⟨((-16628947357/34359738368), (2402127097/17179869184)), (49/34359738368), by norm_num⟩
  | 4 => ⟨((3425393609/8589934592), (-1979254761/17179869184)), (21/17179869184), by norm_num⟩
  | 5 => ⟨((-18063261659/68719476736), (5218640647/68719476736)), (57/68719476736), by norm_num⟩
  | 6 => ⟨((1240282577/8589934592), (-5733262745/137438953472)), (1/2147483648), by norm_num⟩
  | 7 => ⟨((-9343472095/137438953472), (5398828205/274877906944)), (31/137438953472), by norm_num⟩
  | 8 => ⟨((7698639947/274877906944), (-2224207129/274877906944)), (53/549755813888), by norm_num⟩
  | 9 => ⟨((-704818371/68719476736), (1629027523/549755813888)), (5/137438953472), by norm_num⟩
  | 10 => ⟨((7433492387/2199023255552), (-4295207173/4398046511104)), (27/2199023255552), by norm_num⟩
  | 11 => ⟨((-17817875093/17592186044416), (1286936559/4398046511104)), (67/17592186044416), by norm_num⟩
  | 12 => ⟨((19574936535/70368744177664), (-2827688637/35184372088832)), (75/70368744177664), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (-366360640345/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778156782774137/633825300114114700748351602688), (-433284512991/633825300114114700748351602688)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889053545963703/39614081257132168796771975168), (-487340907247/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888785832649515/2475880078570760549798248448), (-517669216487/2475880078570760549798248448)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770452343431871/154742504910672534362390528), (-517522475795/154742504910672534362390528)), (3447/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774430752699465/4835703278458516698824704), (-485021467707/9671406556917033397649408)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((629091765495939/302231454903657293676544), (-424237996885/604462909807314587353088)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886809191694911/75557863725914323419136), (-344547391901/37778931862957161709568)), (4595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296802767472055/4722366482869645213696), (-516565761941/4722366482869645213696)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620435908534741/590295810358705651712), (-354931640277/295147905179352825856)), (4739/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911105232231993/36893488147419103232), (-886707596543/73786976294838206464)), (1481/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455309055689903/2305843009213693952), (-996692223189/9223372036854775808)), (6665/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796243299541957/576460752303423488), (-995626061367/1152921504606846976)), (3333/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193271009905633/144115188075855872), (-869974905511/144115188075855872)), (2917/72057594037927936), by norm_num⟩
  | 4 => ⟨((372419241779299/9007199254740992), (-325642597807/9007199254740992)), (547/2251799813685248), by norm_num⟩
  | 3 => ⟨((743407231744851/4503599627370496), (-1624035648083/9007199254740992)), (171/140737488355328), by norm_num⟩
  | 2 => ⟨((2223083562102759/4503599627370496), (-3235573605729/4503599627370496)), (2737/562949953421312), by norm_num⟩
  | 1 => ⟨((552215381980273/562949953421312), (-4822236018013/2251799813685248)), (16435/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083232784189899/1125899906842624), (-9520690869989/2251799813685248)), (65841/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1083232784189899/1125899906842624), (-9520690869989/2251799813685248)), (251163491255950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((65135153040915/70368744177664), (-18319789202987/2251799813685248)), (63625/1125899906842624), by norm_num⟩
  | 2 => ⟨((964578342281119/1125899906842624), (-2119659600577/140737488355328)), (237643/2251799813685248), by norm_num⟩
  | 3 => ⟨((826115912709791/1125899906842624), (-29055197270009/1125899906842624)), (414345/2251799813685248), by norm_num⟩
  | 4 => ⟨((605403102532815/1125899906842624), (-21318911801839/562949953421312)), (157357/562949953421312), by norm_num⟩
  | 5 => ⟨((323914168869077/1125899906842624), (-183412898699327/4503599627370496)), (90571/281474976710656), by norm_num⟩
  | 6 => ⟨((1461129820953947/18014398509481984), (-824479882173/35184372088832)), (951849/4503599627370496), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-27288066215/1073741824)), (1/536870912), by norm_num⟩, -4, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile017Terms3
