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
namespace Reinmann.XiRectangle.Tile022Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1269/128))
  have he : value ((3/4), (1269/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-311154521/134217728), (-2056536915/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((635862466628445/9007199254740992), (308990906318023/4503599627370496)), (25095535/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3748851545/17179869184), (-910858163/4294967296)), (75/8589934592), by norm_num⟩
  | 2 => ⟨((2896964819/8589934592), (2815501251/8589934592)), (59/4294967296), by norm_num⟩
  | 3 => ⟨((-1492440207/4294967296), (-362618079/1073741824)), (31/2147483648), by norm_num⟩
  | 4 => ⟨((576649505/2147483648), (2241735753/8589934592)), (49/4294967296), by norm_num⟩
  | 5 => ⟨((-2851916961/17179869184), (-2771720153/17179869184)), (123/17179869184), by norm_num⟩
  | 6 => ⟨((2938465467/34359738368), (2855834887/34359738368)), (129/34359738368), by norm_num⟩
  | 7 => ⟨((-1297560215/34359738368), (-1261072411/34359738368)), (29/17179869184), by norm_num⟩
  | 8 => ⟨((2005406855/137438953472), (3898028359/274877906944)), (91/137438953472), by norm_num⟩
  | 9 => ⟨((-2755021211/549755813888), (-2677549143/549755813888)), (127/549755813888), by norm_num⟩
  | 10 => ⟨((3406355009/2199023255552), (3310567229/2199023255552)), (159/2199023255552), by norm_num⟩
  | 11 => ⟨((-119649863/274877906944), (-3721128673/8796093022208)), (181/8796093022208), by norm_num⟩
  | 12 => ⟨((986247483/8796093022208), (239628473/2199023255552)), (189/35184372088832), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395238986543857/2535301200456458802993406410752), (502246973959/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778392780904949/633825300114114700748351602688), (1188288320819/633825300114114700748351602688)), (2885/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889318952069799/39614081257132168796771975168), (1336554971591/39614081257132168796771975168)), (25967/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889067709431171/2475880078570760549798248448), (709876955233/1237940039285380274899124224)), (3449/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885367044222315/77371252455336267181195264), (1419376350455/154742504910672534362390528)), (13797/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774562750707271/4835703278458516698824704), (166283038499/1208925819614629174706176)), (25873/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629207193825585/302231454903657293676544), (290895100761/151115727451828646838272)), (22641/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943592035854057/37778931862957161709568), (1890066857693/75557863725914323419136)), (9199/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648541849174881/2361183241434822606848), (1416893085353/4722366482869645213696)), (13801/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620821816467805/590295810358705651712), (973580443183/295147905179352825856)), (37959/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911346145948609/36893488147419103232), (1216175760621/36893488147419103232)), (47459/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821777512979763/9223372036854775808), (1367098885417/4611686018427387904)), (53405/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593026933595221/1152921504606846976), (682863316787/288230376151711744)), (3339/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193742729275927/144115188075855872), (37295900415/2251799813685248)), (23383/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490382404124081/36028797018963968), (3574247425699/36028797018963968)), (70189/36028797018963968), by norm_num⟩
  | 3 => ⟨((743846260752407/4503599627370496), (557131389441/1125899906842624)), (343/35184372088832), by norm_num⟩
  | 2 => ⟨((69525890770703/140737488355328), (8881908014555/4503599627370496)), (175829/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211451152019011/2251799813685248), (13242656801395/2251799813685248)), (264283/2251799813685248), by norm_num⟩
  | 0 => ⟨((135720907338977/140737488355328), (13083084646063/1125899906842624)), (33171/140737488355328), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((135720907338977/140737488355328), (13083084646063/1125899906842624)), (126537323534917787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2093826219938527/2251799813685248), (12616738721905/562949953421312)), (1035971/2251799813685248), by norm_num⟩
  | 2 => ⟨((1945804107069207/2251799813685248), (93852955082377/2251799813685248)), (1973023/2251799813685248), by norm_num⟩
  | 3 => ⟨((1677478265586929/2251799813685248), (81099334119315/1125899906842624)), (3574289/2251799813685248), by norm_num⟩
  | 4 => ⟨((1237954149652397/2251799813685248), (241659794999413/2251799813685248)), (5840251/2251799813685248), by norm_num⟩
  | 5 => ⟨((654645679941637/2251799813685248), (531421566349747/4503599627370496)), (15350063/4503599627370496), by norm_num⟩
  | 6 => ⟨((635862466628445/9007199254740992), (308990906318023/4503599627370496)), (25095535/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-311154521/134217728), (-2056536915/67108864)), (1/67108864), by norm_num⟩, -5, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-157814591/67108864), (-2086111627/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((202805086055499/2251799813685248), (278262843392841/9007199254740992)), (35694093/18014398509481984), by norm_num⟩
  | 1 => ⟨((-303217971/1073741824), (-832072769/8589934592)), (109/17179869184), by norm_num⟩
  | 2 => ⟨((3802952777/8589934592), (1304479677/8589934592)), (87/8589934592), by norm_num⟩
  | 3 => ⟨((-3974712145/8589934592), (-1363396161/8589934592)), (93/8589934592), by norm_num⟩
  | 4 => ⟨((3115671735/8589934592), (534365097/4294967296)), (37/4294967296), by norm_num⟩
  | 5 => ⟨((-3907668281/17179869184), (-1340398937/17179869184)), (95/17179869184), by norm_num⟩
  | 6 => ⟨((2042078549/17179869184), (1400937705/34359738368)), (101/34359738368), by norm_num⟩
  | 7 => ⟨((-3658814559/68719476736), (-1255037735/68719476736)), (23/17179869184), by norm_num⟩
  | 8 => ⟨((5736095943/274877906944), (1967581779/274877906944)), (147/274877906944), by norm_num⟩
  | 9 => ⟨((-3996776811/549755813888), (-1370964731/549755813888)), (105/549755813888), by norm_num⟩
  | 10 => ⟨((5012748229/2199023255552), (859730397/1099511627776)), (67/1099511627776), by norm_num⟩
  | 11 => ⟨((-2857716923/4398046511104), (-980247159/4398046511104)), (155/8796093022208), by norm_num⟩
  | 12 => ⟨((2986784961/17592186044416), (2049039531/35184372088832)), (41/8796093022208), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518636921/10141204801825835211973625643008), (215218091949/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444585506575295/158456325028528675187087900672), (509165971069/633825300114114700748351602688)), (2883/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889261899257313/39614081257132168796771975168), (286347460287/19807040628566084398385987584)), (25947/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889007150763829/2475880078570760549798248448), (608342448081/2475880078570760549798248448)), (13785/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770673597159197/154742504910672534362390528), (76022297125/19342813113834066795298816)), (27571/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387267215595799/2417851639229258349412352), (569992965153/9671406556917033397649408)), (25849/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157295612499669/75557863725914323419136), (249284825635/302231454903657293676544)), (22619/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887103788224085/75557863725914323419136), (202462304941/18889465931478580854784)), (36757/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297023602839595/4722366482869645213696), (303550703957/2361183241434822606848)), (13785/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810369687617075/295147905179352825856), (417150382895/295147905179352825856)), (37911/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822589525145921/73786976294838206464), (1042180939377/73786976294838206464)), (23697/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821662291406241/9223372036854775808), (1171498698437/9223372036854775808)), (13331/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99557012496967/72057594037927936), (1170306311175/1152921504606846976)), (13333/288230376151711744), by norm_num⟩
  | 5 => ⟨((74602680318459/9007199254740992), (1022678215147/144115188075855872)), (23337/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490233730465715/36028797018963968), (1531341774445/36028797018963968)), (70029/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487508584986951/9007199254740992), (238688017791/1125899906842624)), (87567/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224466322298265/4503599627370496), (3805025519043/4503599627370496)), (175227/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210922014502501/2251799813685248), (1418177162535/562949953421312)), (131539/1125899906842624), by norm_num⟩
  | 0 => ⟨((2170532245243307/2251799813685248), (350214370869/70368744177664)), (527117/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2170532245243307/2251799813685248), (350214370869/70368744177664)), (2010791787154387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2092141852620013/2251799813685248), (10802403731969/1125899906842624)), (510717/1125899906842624), by norm_num⟩
  | 2 => ⟨((971798367061793/1125899906842624), (10036487621679/562949953421312)), (1917625/2251799813685248), by norm_num⟩
  | 3 => ⟨((1676861568513827/2251799813685248), (69302375619767/2251799813685248)), (1689349/1125899906842624), by norm_num⟩
  | 4 => ⟨((623292950739287/1125899906842624), (103215649612573/2251799813685248)), (5240041/2251799813685248), by norm_num⟩
  | 5 => ⟨((171343266179869/562949953421312), (228558813864385/4503599627370496)), (1570525/562949953421312), by norm_num⟩
  | 6 => ⟨((202805086055499/2251799813685248), (278262843392841/9007199254740992)), (35694093/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-157814591/67108864), (-2086111627/67108864)), (1/67108864), by norm_num⟩, -5, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-319913373/134217728), (-4228854905/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((103400083347723/1125899906842624), (-75898936382271/9007199254740992)), (28087505/18014398509481984), by norm_num⟩
  | 1 => ⟨((-5014206405/17179869184), (460073291/17179869184)), (87/17179869184), by norm_num⟩
  | 2 => ⟨((995963617/2147483648), (-365534421/8589934592)), (71/8589934592), by norm_num⟩
  | 3 => ⟨((-4220301317/8589934592), (96807339/2147483648)), (77/8589934592), by norm_num⟩
  | 4 => ⟨((6706172383/17179869184), (-615317869/17179869184)), (31/4294967296), by norm_num⟩
  | 5 => ⟨((-2131257683/8589934592), (195551331/8589934592)), (5/1073741824), by norm_num⟩
  | 6 => ⟨((4515501095/34359738368), (-12947347/1073741824)), (43/17179869184), by norm_num⟩
  | 7 => ⟨((-4100144443/68719476736), (376204487/68719476736)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((1628809969/68719476736), (-597799055/274877906944)), (129/274877906944), by norm_num⟩
  | 9 => ⟨((-4601285121/549755813888), (26386633/34359738368)), (93/549755813888), by norm_num⟩
  | 10 => ⟨((5849252721/2199023255552), (-4192907/17179869184)), (15/274877906944), by norm_num⟩
  | 11 => ⟨((-3379861821/4398046511104), (38764463/549755813888)), (141/8796093022208), by norm_num⟩
  | 12 => ⟨((7160921871/35184372088832), (-328521467/17592186044416)), (151/35184372088832), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98804433728147/633825300114114700748351602688), (-119186056647/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778292971773833/633825300114114700748351602688), (-140978589187/633825300114114700748351602688)), (11527/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889206731397085/39614081257132168796771975168), (-158568170843/39614081257132168796771975168)), (25937/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944474279256643/1237940039285380274899124224), (-5263679283/77371252455336267181195264)), (27557/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885307515720943/77371252455336267181195264), (-84195847653/77371252455336267181195264)), (13779/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96813374075035/604462909807314587353088), (-4931822275/302231454903657293676544)), (6459/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78644806913993/37778931862957161709568), (-138042142193/604462909807314587353088)), (22607/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887025858260735/75557863725914323419136), (-224226870809/75557863725914323419136)), (287/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1296965201505585/4722366482869645213696), (-84045018341/2361183241434822606848)), (27553/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810329574155663/295147905179352825856), (-230993690975/590295810358705651712)), (18943/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822489353748301/73786976294838206464), (-288547088951/73786976294838206464)), (23679/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821549752755205/9223372036854775808), (-324347542393/9223372036854775808)), (53279/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592799853743985/1152921504606846976), (-324012965795/1152921504606846976)), (26641/576460752303423488), by norm_num⟩
  | 5 => ⟨((596772399145649/72057594037927936), (-141567706169/72057594037927936)), (46625/144115188075855872), by norm_num⟩
  | 4 => ⟨((745043515793763/18014398509481984), (-211976208159/18014398509481984)), (34971/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487325964131333/9007199254740992), (-33039337789/562949953421312)), (87437/9007199254740992), by norm_num⟩
  | 2 => ⟨((556025832627119/1125899906842624), (-1053335892585/4503599627370496)), (174901/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210383122652091/2251799813685248), (-1570232957709/2251799813685248)), (262425/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169476671843583/2251799813685248), (-3101600081099/2251799813685248)), (65645/281474976710656), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2169476671843583/2251799813685248), (-3101600081099/2251799813685248)), (250415803075694949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((522539723685261/562949953421312), (-747052311271/281474976710656)), (1013369/2251799813685248), by norm_num⟩
  | 2 => ⟨((970052591073219/1125899906842624), (-11094826627129/2251799813685248)), (235829/281474976710656), by norm_num⟩
  | 3 => ⟨((1671500725658949/2251799813685248), (-4779539127655/562949953421312)), (3269561/2251799813685248), by norm_num⟩
  | 4 => ⟨((1240585044457467/2251799813685248), (-28382640665081/2251799813685248)), (613685/281474976710656), by norm_num⟩
  | 5 => ⟨((1366236615610117/4503599627370496), (-15636860487027/1125899906842624)), (5533327/2251799813685248), by norm_num⟩
  | 6 => ⟨((103400083347723/1125899906842624), (-75898936382271/9007199254740992)), (28087505/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-319913373/134217728), (-4228854905/134217728)), (1/67108864), by norm_num⟩, -5, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-162011325/67108864), (-1070793601/33554432)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((708464356765663/9007199254740992), (-191778102234553/4503599627370496)), (9523073/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4349629957/17179869184), (294356297/2147483648)), (15/4294967296), by norm_num⟩
  | 2 => ⟨((3500229679/8589934592), (-1894992737/8589934592)), (25/4294967296), by norm_num⟩
  | 3 => ⟨((-3755601565/8589934592), (1016624385/4294967296)), (55/8589934592), by norm_num⟩
  | 4 => ⟨((3022203771/8589934592), (-409048457/2147483648)), (23/4294967296), by norm_num⟩
  | 5 => ⟨((-3891239463/17179869184), (2106681903/17179869184)), (61/17179869184), by norm_num⟩
  | 6 => ⟨((4175138879/34359738368), (-2260382483/34359738368)), (67/34359738368), by norm_num⟩
  | 7 => ⟨((-479973343/8589934592), (1039412933/34359738368)), (1/1073741824), by norm_num⟩
  | 8 => ⟨((3089949181/137438953472), (-1672870581/137438953472)), (53/137438953472), by norm_num⟩
  | 9 => ⟨((-1105129191/137438953472), (1196613927/274877906944)), (77/549755813888), by norm_num⟩
  | 10 => ⟨((2845818909/1099511627776), (-1540700657/1099511627776)), (51/1099511627776), by norm_num⟩
  | 11 => ⟨((-3331031887/4398046511104), (1803390581/4398046511104)), (61/4398046511104), by norm_num⟩
  | 12 => ⟨((1787029669/8796093022208), (-241870431/2199023255552)), (67/17592186044416), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98801941140089/633825300114114700748351602688), (-646368369337/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778245496887853/633825300114114700748351602688), (-191128678671/158456325028528675187087900672)), (721/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889153316402629/39614081257132168796771975168), (-859899197353/39614081257132168796771975168)), (6489/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888891796671177/2475880078570760549798248448), (-913417994741/2475880078570760549798248448)), (6895/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770558260157071/154742504910672534362390528), (-114145636627/19342813113834066795298816)), (6895/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48405023503179/302231454903657293676544), (-855823664367/9671406556917033397649408)), (12929/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258270321658363/604462909807314587353088), (-748577205991/604462909807314587353088)), (5657/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943475066233297/37778931862957161709568), (-607967377633/37778931862957161709568)), (9193/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81056774425491/295147905179352825856), (-28484718627/147573952589676412928)), (13791/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620581007090419/590295810358705651712), (-1252612942803/590295810358705651712)), (18965/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822391637560923/73786976294838206464), (-1564694928577/73786976294838206464)), (11855/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821439767682277/9223372036854775808), (-879405034267/4611686018427387904)), (13339/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796344900488047/576460752303423488), (-1756972272941/1152921504606846976)), (6671/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193448426316199/144115188075855872), (-1535285776265/144115188075855872)), (23355/144115188075855872), by norm_num⟩
  | 4 => ⟨((372485580725129/9007199254740992), (-1149402562241/18014398509481984)), (35045/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487144816483795/9007199254740992), (-2866304554099/9007199254740992)), (43829/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223740257734095/4503599627370496), (-1427765202621/1125899906842624)), (5483/281474976710656), by norm_num⟩
  | 1 => ⟨((1104918298634657/1125899906842624), (-4256460173307/1125899906842624)), (131767/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084188060019623/1125899906842624), (-16812352289311/2251799813685248)), (264243/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1084188060019623/1125899906842624), (-16812352289311/2251799813685248)), (1008007058150481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2087917546752285/2251799813685248), (-16189495622245/1125899906842624)), (256427/1125899906842624), by norm_num⟩
  | 2 => ⟨((120968548593727/140737488355328), (-15011250901311/562949953421312)), (60363/140737488355328), by norm_num⟩
  | 3 => ⟨((103876417835533/140737488355328), (-103221352339225/2251799813685248)), (1711797/2251799813685248), by norm_num⟩
  | 4 => ⟨((610992314320685/1125899906842624), (-152372540542531/2251799813685248)), (2683845/2251799813685248), by norm_num⟩
  | 5 => ⟨((1305648071014433/4503599627370496), (-165376070500051/2251799813685248)), (6552203/4503599627370496), by norm_num⟩
  | 6 => ⟨((708464356765663/9007199254740992), (-191778102234553/4503599627370496)), (9523073/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/67108864), (-1070793601/33554432)), (1/134217728), by norm_num⟩, -5, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-20498171/8388608), (-4335363169/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((495378943281169/9007199254740992), (-1210875299789187/18014398509481984)), (23689125/9007199254740992), by norm_num⟩
  | 1 => ⟨((-769611559/4294967296), (3762386915/17179869184)), (149/17179869184), by norm_num⟩
  | 2 => ⟨((626867189/2147483648), (-1532277473/4294967296)), (123/8589934592), by norm_num⟩
  | 3 => ⟨((-1361595879/4294967296), (3328205287/8589934592)), (17/1073741824), by norm_num⟩
  | 4 => ⟨((1109052705/4294967296), (-2710903531/8589934592)), (7/536870912), by norm_num⟩
  | 5 => ⟨((-2890720623/17179869184), (883238541/4294967296)), (37/4294967296), by norm_num⟩
  | 6 => ⟨((1569707809/17179869184), (-1918450955/17179869184)), (163/34359738368), by norm_num⟩
  | 7 => ⟨((-2922434045/68719476736), (892928345/17179869184)), (77/34359738368), by norm_num⟩
  | 8 => ⟨((2380393061/137438953472), (-1454623375/68719476736)), (127/137438953472), by norm_num⟩
  | 9 => ⟨((-3446911285/549755813888), (2106357059/274877906944)), (93/274877906944), by norm_num⟩
  | 10 => ⟨((2246073945/1099511627776), (-2745085857/1099511627776)), (123/1099511627776), by norm_num⟩
  | 11 => ⟨((-2661063907/4398046511104), (1626137223/2199023255552)), (147/4398046511104), by norm_num⟩
  | 12 => ⟨((1445000517/8796093022208), (-220754669/1099511627776)), (81/8796093022208), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395198185306375/2535301200456458802993406410752), (-1152871454521/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778199493989445/633825300114114700748351602688), (-1363532655233/633825300114114700748351602688)), (5771/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889101536073113/39614081257132168796771975168), (-1533649183455/39614081257132168796771975168)), (6493/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888836743367699/2475880078570760549798248448), (-814548095499/1237940039285380274899124224)), (13799/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770503165615333/154742504910672534362390528), (-407159891147/38685626227668133590597632)), (1725/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548909057192269/9671406556917033397649408), (-763182299789/4835703278458516698824704)), (25879/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258225044880009/604462909807314587353088), (-1335084227465/604462909807314587353088)), (22647/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886876475796621/75557863725914323419136), (-1084301644629/37778931862957161709568)), (18403/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324213269182931/1180591620717411303424), (-1625657873215/4722366482869645213696)), (13805/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810252417051709/295147905179352825856), (-2233989136851/590295810358705651712)), (37971/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822296247434363/73786976294838206464), (-2790552119917/73786976294838206464)), (11869/18446744073709551616), by norm_num⟩
  | 7 => ⟨((889322370695/4503599627370496), (-392089209301/1152921504606846976)), (53427/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592581950961999/1152921504606846976), (-195837196951/72057594037927936)), (53447/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596676861934545/72057594037927936), (-2737991954797/144115188075855872)), (23395/72057594037927936), by norm_num⟩
  | 4 => ⟨((744899802202175/18014398509481984), (-2049770826529/18014398509481984)), (70231/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486965260628137/9007199254740992), (-5111421521843/9007199254740992)), (43935/4503599627370496), by norm_num⟩
  | 2 => ⟨((138961105973661/281474976710656), (-1272990998791/562949953421312)), (175987/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209284207258533/2251799813685248), (-3794739750529/562949953421312)), (132299/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083618813119287/1125899906842624), (-14986153472345/1125899906842624)), (265843/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1083618813119287/1125899906842624), (-14986153472345/1125899906842624)), (1014110569480514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521363018246637/562949953421312), (-28846752256097/1125899906842624)), (518797/1125899906842624), by norm_num⟩
  | 2 => ⟨((241239351176425/281474976710656), (-106862997191483/2251799813685248)), (1975057/2251799813685248), by norm_num⟩
  | 3 => ⟨((1648970502995037/2251799813685248), (-183174791652913/2251799813685248)), (3572923/2251799813685248), by norm_num⟩
  | 4 => ⟨((1192624095236735/2251799813685248), (-134137069597491/1125899906842624)), (2907059/1125899906842624), by norm_num⟩
  | 5 => ⟨((1199379456887357/4503599627370496), (-568345730536687/4503599627370496)), (7544041/2251799813685248), by norm_num⟩
  | 6 => ⟨((495378943281169/9007199254740992), (-1210875299789187/18014398509481984)), (23689125/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20498171/8388608), (-4335363169/134217728)), (1/67108864), by norm_num⟩, -5, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-165884901/67108864), (-2192791035/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((58282791676237/2251799813685248), (-90478257283763/1125899906842624)), (27569625/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1465534771/17179869184), (4550194945/17179869184)), (11/2147483648), by norm_num⟩
  | 2 => ⟨((603770441/4294967296), (-1874587531/4294967296)), (37/4294967296), by norm_num⟩
  | 3 => ⟨((-331654813/2147483648), (4118889795/8589934592)), (83/8589934592), by norm_num⟩
  | 4 => ⟨((1093080159/8589934592), (-424224651/1073741824)), (35/4294967296), by norm_num⟩
  | 5 => ⟨((-720522777/8589934592), (4474160781/17179869184)), (47/8589934592), by norm_num⟩
  | 6 => ⟨((791575177/17179869184), (-4915368015/34359738368)), (105/34359738368), by norm_num⟩
  | 7 => ⟨((-1490801515/68719476736), (4628643175/68719476736)), (101/68719476736), by norm_num⟩
  | 8 => ⟨((38386239/4294967296), (-953453301/34359738368)), (85/137438953472), by norm_num⟩
  | 9 => ⟨((-1799321339/549755813888), (2793268035/274877906944)), (63/274877906944), by norm_num⟩
  | 10 => ⟨((1186053921/1099511627776), (-1841231153/549755813888)), (85/1099511627776), by norm_num⟩
  | 11 => ⟨((-1421469177/4398046511104), (4413380009/4398046511104)), (13/549755813888), by norm_num⟩
  | 12 => ⟨((780821753/8796093022208), (-606074189/2199023255552)), (29/4398046511104), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (-410064147457/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((13891834893637/4951760157141521099596496896), (-1939885728539/633825300114114700748351602688)), (5775/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944525642065199/19807040628566084398385987584), (-545475675619/9903520314283042199192993792)), (12995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236097911111309/309485009821345068724781056), (-289710886381/309485009821345068724781056)), (13809/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885224820855073/77371252455336267181195264), (-2317029763267/154742504910672534362390528)), (13811/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774429402413263/4835703278458516698824704), (-1085758616795/4835703278458516698824704)), (6475/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258181000425815/604462909807314587353088), (-1899379681405/604462909807314587353088)), (11333/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943402382822055/37778931862957161709568), (-3085184000235/75557863725914323419136)), (4605/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648399586795849/2361183241434822606848), (-2312744092293/4722366482869645213696)), (13819/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810215260855877/295147905179352825856), (-3178165356795/590295810358705651712)), (9503/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455550766018285/18446744073709551616), (-992480482515/18446744073709551616)), (11883/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821226981998003/9223372036854775808), (-557792023255/1152921504606846976)), (6687/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398119054146683/288230376151711744), (-4457558302569/1152921504606846976)), (26763/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193260644085623/144115188075855872), (-3894994712267/144115188075855872)), (11717/72057594037927936), by norm_num⟩
  | 4 => ⟨((744829432197199/18014398509481984), (-5831770236505/36028797018963968)), (2199/2251799813685248), by norm_num⟩
  | 3 => ⟨((371696846044161/2251799813685248), (-3635492514897/4503599627370496)), (44039/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223016124830587/4503599627370496), (-14485928275179/4503599627370496)), (44125/2251799813685248), by norm_num⟩
  | 1 => ⟨((2208727433660823/2251799813685248), (-21589282138515/2251799813685248)), (132813/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083033583923943/1125899906842624), (-21311539721957/1125899906842624)), (267387/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1083033583923943/1125899906842624), (-21311539721957/1125899906842624)), (1020000466353606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1041395913665095/1125899906842624), (-82000586743933/2251799813685248)), (524537/2251799813685248), by norm_num⟩
  | 2 => ⟨((961741286557479/1125899906842624), (-151692127220699/2251799813685248)), (252135/562949953421312), by norm_num⟩
  | 3 => ⟨((1632815974701973/2251799813685248), (-259150179704683/2251799813685248)), (1858867/2251799813685248), by norm_num⟩
  | 4 => ⟨((1154156411154343/2251799813685248), (-46978482578363/281474976710656)), (48807/35184372088832), by norm_num⟩
  | 5 => ⟨((1057669898849835/4503599627370496), (-770519887597065/4503599627370496)), (4244723/2251799813685248), by norm_num⟩
  | 6 => ⟨((58282791676237/2251799813685248), (-90478257283763/1125899906842624)), (27569625/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-2192791035/67108864)), (1/134217728), by norm_num⟩, -5, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile022Terms3
