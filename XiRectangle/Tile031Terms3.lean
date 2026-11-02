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
namespace Reinmann.XiRectangle.Tile031Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨31,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8037/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8037/640))
  have he : value ((5/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-259295435/134217728), (-2604946759/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((571313999635119/9007199254740992), (-1173180071248447/9007199254740992)), (44101665/9007199254740992), by norm_num⟩
  | 1 => ⟨((-421036679/2147483648), (3458356291/8589934592)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((1301442249/4294967296), (-5344963057/8589934592)), (103/4294967296), by norm_num⟩
  | 3 => ⟨((-2681875495/8589934592), (688396155/1073741824)), (107/4294967296), by norm_num⟩
  | 4 => ⟨((259055969/1073741824), (-531965435/1073741824)), (21/1073741824), by norm_num⟩
  | 5 => ⟨((-1281204797/8589934592), (5261848779/17179869184)), (105/8589934592), by norm_num⟩
  | 6 => ⟨((2640172279/34359738368), (-5421532653/34359738368)), (219/34359738368), by norm_num⟩
  | 7 => ⟨((-1165840657/34359738368), (2394026799/34359738368)), (195/68719476736), by norm_num⟩
  | 8 => ⟨((900915741/68719476736), (-3700019235/137438953472)), (153/137438953472), by norm_num⟩
  | 9 => ⟨((-2475350047/549755813888), (5083074015/549755813888)), (53/137438953472), by norm_num⟩
  | 10 => ⟨((95642651/68719476736), (-3142399515/1099511627776)), (133/1099511627776), by norm_num⟩
  | 11 => ⟨((-1720061059/4398046511104), (1766052783/2199023255552)), (151/4398046511104), by norm_num⟩
  | 12 => ⟨((1772260585/17592186044416), (-3639296085/17592186044416)), (157/17592186044416), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790729624827833/5070602400912917605986812821504), (-1455824460599/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889493766158377/316912650057057350374175801344), (-1723298364319/633825300114114700748351602688)), (23093/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889987875192369/39614081257132168796771975168), (-1938381147095/39614081257132168796771975168)), (25983/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59055569521583/77371252455336267181195264), (-128695248251/154742504910672534362390528)), (13805/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885722180653923/77371252455336267181195264), (-2058667357971/154742504910672534362390528)), (27613/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549791124773351/9671406556917033397649408), (-1929515623169/9671406556917033397649408)), (25891/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258996550747211/604462909807314587353088), (-26372520137/9444732965739290427392)), (11329/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944064802224817/37778931862957161709568), (-1370916623057/37778931862957161709568)), (18413/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297792426130867/4722366482869645213696), (-1027789998527/2361183241434822606848)), (27627/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405448908052565/147573952589676412928), (-88285352917/18446744073709551616)), (9499/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911954267444381/36893488147419103232), (-1764739155693/36893488147419103232)), (23755/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823144375866455/9223372036854775808), (-3968002989971/9223372036854775808)), (53469/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797196017602351/576460752303423488), (-991170070887/288230376151711744)), (53495/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194935214249223/144115188075855872), (-3465360544397/144115188075855872)), (23419/72057594037927936), by norm_num⟩
  | 4 => ⟨((186520897495185/4503599627370496), (-5190579754853/36028797018963968)), (70315/36028797018963968), by norm_num⟩
  | 3 => ⟨((744958294999547/4503599627370496), (-6475186594377/9007199254740992)), (21999/2251799813685248), by norm_num⟩
  | 2 => ⟨((557313998448195/1125899906842624), (-6455666916103/2251799813685248)), (44075/1125899906842624), by norm_num⟩
  | 1 => ⟨((2218040961796665/2251799813685248), (-19269664225987/2251799813685248)), (33153/281474976710656), by norm_num⟩
  | 0 => ⟨((2184509612129209/2251799813685248), (-19075775092287/1125899906842624)), (533553/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2184509612129209/2251799813685248), (-19075775092287/1125899906842624)), (2035343178755950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1059291921890675/1125899906842624), (-74022946080127/2251799813685248)), (526649/1125899906842624), by norm_num⟩
  | 2 => ⟨((995407779887931/1125899906842624), (-139287530517911/2251799813685248)), (2051221/2251799813685248), by norm_num⟩
  | 3 => ⟨((1751463674931797/2251799813685248), (-246288130368033/2251799813685248)), (1940365/1125899906842624), by norm_num⟩
  | 4 => ⟨((333840417692845/562949953421312), (-383128829911851/2251799813685248)), (6885813/2251799813685248), by norm_num⟩
  | 5 => ⟨((726708955880765/2251799813685248), (-14200184207163/70368744177664)), (5254999/1125899906842624), by norm_num⟩
  | 6 => ⟨((571313999635119/9007199254740992), (-1173180071248447/9007199254740992)), (44101665/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-259295435/134217728), (-2604946759/67108864)), (1/67108864), by norm_num⟩, -6, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-263024319/134217728), (-2642408061/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-133065922375843/9007199254740992), (-1262145917489055/9007199254740992)), (26227255/4503599627370496), by norm_num⟩
  | 1 => ⟨((99474771/2147483648), (7548239181/17179869184)), (79/4294967296), by norm_num⟩
  | 2 => ⟨((-311902569/4294967296), (-5916865073/8589934592)), (249/8589934592), by norm_num⟩
  | 3 => ⟨((325989567/4294967296), (3092049369/4294967296)), (131/4294967296), by norm_num⟩
  | 4 => ⟨((-511069201/8589934592), (-151485983/268435456)), (207/8589934592), by norm_num⟩
  | 5 => ⟨((640981809/17179869184), (6079787821/17179869184)), (131/8589934592), by norm_num⟩
  | 6 => ⟨((-669931585/34359738368), (-6354379849/34359738368)), (69/8589934592), by norm_num⟩
  | 7 => ⟨((600161889/68719476736), (5692606075/68719476736)), (249/68719476736), by norm_num⟩
  | 8 => ⟨((-470451033/137438953472), (-4462283355/137438953472)), (197/137438953472), by norm_num⟩
  | 9 => ⟨((655598441/549755813888), (6218428289/549755813888)), (277/549755813888), by norm_num⟩
  | 10 => ⟨((-12847657/34359738368), (-1949784593/549755813888)), (175/1099511627776), by norm_num⟩
  | 11 => ⟨((468756413/4398046511104), (4446209683/4398046511104)), (101/2199023255552), by norm_num⟩
  | 12 => ⟨((-244963837/8796093022208), (-4647021581/17592186044416)), (213/17592186044416), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581423060041861/10141204801825835211973625643008), (-545741074403/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222367838882271/79228162514264337593543950336), (-1291957395495/316912650057057350374175801344)), (11557/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889937347021525/39614081257132168796771975168), (-726600017791/9903520314283042199192993792)), (3251/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889724402849305/2475880078570760549798248448), (-3087432205613/2475880078570760549798248448)), (13819/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885695193484917/77371252455336267181195264), (-3086737258935/154742504910672534362390528)), (27643/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387435090476521/2417851639229258349412352), (-723269491835/2417851639229258349412352)), (25921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((4917781138391/2361183241434822606848), (-158169074835/37778931862957161709568)), (22687/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472014214976589/18889465931478580854784), (-4111012551841/75557863725914323419136)), (9219/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648868801355891/2361183241434822606848), (-770512336357/1180591620717411303424)), (27667/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621719819823035/590295810358705651712), (-529481530101/73786976294838206464)), (4757/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823813124926499/73786976294838206464), (-5291868203139/73786976294838206464)), (47593/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823036154801441/9223372036854775808), (-5949301606715/9223372036854775808)), (53573/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398570677504015/288230376151711744), (-5944242160169/1152921504606846976)), (13403/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194838315245711/144115188075855872), (-2597762209587/72057594037927936)), (23477/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492019359208931/36028797018963968), (-7781922698339/36028797018963968)), (70519/36028797018963968), by norm_num⟩
  | 3 => ⟨((744863751314413/4503599627370496), (-4853770629185/4503599627370496)), (88303/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228864944646363/4503599627370496), (-19355595166455/4503599627370496)), (88533/2251799813685248), by norm_num⟩
  | 1 => ⟨((554355602767295/562949953421312), (-28885020574087/2251799813685248)), (133379/1125899906842624), by norm_num⟩
  | 0 => ⟨((1091572926013107/1125899906842624), (-57178627427027/2251799813685248)), (538163/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1091572926013107/1125899906842624), (-57178627427027/2251799813685248)), (2052928933150481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((132195821394699/140737488355328), (-110870675566469/2251799813685248)), (535421/1125899906842624), by norm_num⟩
  | 2 => ⟨((1981302190321239/2251799813685248), (-208283382009633/2251799813685248)), (2117151/2251799813685248), by norm_num⟩
  | 3 => ⟨((431008162732379/562949953421312), (-183263324952421/1125899906842624)), (4117315/2251799813685248), by norm_num⟩
  | 4 => ⟨((315075387600293/562949953421312), (-280621708924293/1125899906842624)), (7644989/2251799813685248), by norm_num⟩
  | 5 => ⟨((282744011285193/1125899906842624), (-314120262986173/1125899906842624)), (3092125/562949953421312), by norm_num⟩
  | 6 => ⟨((-133065922375843/9007199254740992), (-1262145917489055/9007199254740992)), (26227255/4503599627370496), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-263024319/134217728), (-2642408061/67108864)), (1/67108864), by norm_num⟩, -6, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-133297239/67108864), (-2678274773/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-368765309965437/4503599627370496), (-991623623692489/9007199254740992)), (6974849/1125899906842624), by norm_num⟩
  | 1 => ⟨((2235328685/8589934592), (751360239/2147483648)), (171/8589934592), by norm_num⟩
  | 2 => ⟨((-3551997445/8589934592), (-4775726571/8589934592)), (137/4294967296), by norm_num⟩
  | 3 => ⟨((940703257/2147483648), (632396505/1073741824)), (147/4294967296), by norm_num⟩
  | 4 => ⟨((-2989605589/8589934592), (-2009790135/4294967296)), (235/8589934592), by norm_num⟩
  | 5 => ⟨((1900225499/8589934592), (2554888495/8589934592)), (151/8589934592), by norm_num⟩
  | 6 => ⟨((-2013006309/17179869184), (-2706524389/17179869184)), (81/8589934592), by norm_num⟩
  | 7 => ⟨((1827840689/34359738368), (614391443/8589934592)), (297/68719476736), by norm_num⟩
  | 8 => ⟨((-2904488051/137438953472), (-3905138157/137438953472)), (119/68719476736), by norm_num⟩
  | 9 => ⟨((1025624375/137438953472), (1378971031/137438953472)), (85/137438953472), by norm_num⟩
  | 10 => ⟨((-2607591579/1099511627776), (-1752977667/549755813888)), (109/549755813888), by norm_num⟩
  | 11 => ⟨((3013478693/4398046511104), (4051678101/4398046511104)), (127/2199023255552), by norm_num⟩
  | 12 => ⟨((-3192332501/17592186044416), (-4292150369/17592186044416)), (271/17592186044416), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395347102722001/2535301200456458802993406410752), (-1439576231573/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778899056640597/633825300114114700748351602688), (-851955998117/158456325028528675187087900672)), (11567/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889888094284751/39614081257132168796771975168), (-3833122978891/39614081257132168796771975168)), (1627/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889671887502219/2475880078570760549798248448), (-4071866580091/2475880078570760549798248448)), (27665/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771337664427315/154742504910672534362390528), (-4070936802073/154742504910672534362390528)), (3459/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549690714517983/9671406556917033397649408), (-1907757770259/4835703278458516698824704)), (12975/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258908310117209/604462909807314587353088), (-3337588586261/604462909807314587353088)), (11357/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471996374600093/18889465931478580854784), (-5421730292753/75557863725914323419136)), (36923/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297683721526827/4722366482869645213696), (-4064678379209/4722366482869645213696)), (27705/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405411287183241/147573952589676412928), (-5586302139573/590295810358705651712)), (19057/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455929727618375/18446744073709551616), (-6978933120443/73786976294838206464)), (5959/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822928961392389/9223372036854775808), (-7845878264131/9223372036854775808)), (6709/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797087008299523/576460752303423488), (-7839104792825/1152921504606846976)), (13431/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194741524676581/144115188075855872), (-3425800607007/72057594037927936)), (23533/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491870814885033/36028797018963968), (-641386409711/2251799813685248)), (35357/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489535965544489/9007199254740992), (-12801120803973/9007199254740992)), (22149/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114232191430821/2251799813685248), (-12761262401747/2251799813685248)), (88901/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108389068574955/1125899906842624), (-19042432139141/1125899906842624)), (134115/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090842650282947/1125899906842624), (-37688126871925/1125899906842624)), (4239/17592186044416), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1090842650282947/1125899906842624), (-37688126871925/1125899906842624)), (16170501776093239/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((263903852719507/281474976710656), (-73029255889115/1125899906842624)), (543861/1125899906842624), by norm_num⟩
  | 2 => ⟨((492490769706797/562949953421312), (-273881567954621/2251799813685248)), (2180749/2251799813685248), by norm_num⟩
  | 3 => ⟨((845044793846175/1125899906842624), (-14975148255933/70368744177664)), (4346091/2251799813685248), by norm_num⟩
  | 4 => ⟨((145814784001221/281474976710656), (-359667384110219/1125899906842624)), (8373703/2251799813685248), by norm_num⟩
  | 5 => ⟨((187255182507041/1125899906842624), (-372642872479757/1125899906842624)), (14025735/2251799813685248), by norm_num⟩
  | 6 => ⟨((-368765309965437/4503599627370496), (-991623623692489/9007199254740992)), (6974849/1125899906842624), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-133297239/67108864), (-2678274773/67108864)), (1/67108864), by norm_num⟩, -6, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-270018875/134217728), (-5425354245/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1100648676568251/9007199254740992), (-244879348697927/4503599627370496)), (13379605/2251799813685248), by norm_num⟩
  | 1 => ⟨((3378726403/8589934592), (375860317/2147483648)), (83/4294967296), by norm_num⟩
  | 2 => ⟨((-5437850369/8589934592), (-151230961/536870912)), (269/8589934592), by norm_num⟩
  | 3 => ⟨((1458647091/2147483648), (2596232983/8589934592)), (291/8589934592), by norm_num⟩
  | 4 => ⟨((-2347601929/4294967296), (-261154737/1073741824)), (59/2147483648), by norm_num⟩
  | 5 => ⟨((1511327819/4294967296), (1344999471/8589934592)), (77/4294967296), by norm_num⟩
  | 6 => ⟨((-3243184387/17179869184), (-1443128761/17179869184)), (167/17179869184), by norm_num⟩
  | 7 => ⟨((745671987/8589934592), (1327214937/34359738368)), (155/34359738368), by norm_num⟩
  | 8 => ⟨((-4800451065/137438953472), (-1068035019/68719476736)), (63/34359738368), by norm_num⟩
  | 9 => ⟨((858447549/68719476736), (1527943157/274877906944)), (91/137438953472), by norm_num⟩
  | 10 => ⟨((-1105294425/274877906944), (-491825929/274877906944)), (59/274877906944), by norm_num⟩
  | 11 => ⟨((5053701/4294967296), (1151364795/2199023255552)), (139/2199023255552), by norm_num⟩
  | 12 => ⟨((-694068735/2199023255552), (-77210423/549755813888)), (301/17592186044416), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581355176385417/10141204801825835211973625643008), (-3546916728475/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889428251704769/316912650057057350374175801344), (-2099013372161/316912650057057350374175801344)), (11577/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944920023995783/19807040628566084398385987584), (-4721925024717/39614081257132168796771975168)), (26055/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118101288220279/154742504910672534362390528), (-19593800977/9671406556917033397649408)), (27691/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771286133495029/154742504910672534362390528), (-5014851765881/154742504910672534362390528)), (6925/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193705266694455/1208925819614629174706176), (-4700189816905/9671406556917033397649408)), (12989/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314716382814877/151115727451828646838272), (-1027858136389/151115727451828646838272)), (5685/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887915475959683/75557863725914323419136), (-6678765351309/75557863725914323419136)), (4621/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((40550961302149/147573952589676412928), (-2503525452865/2361183241434822606848)), (13871/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405392902448777/147573952589676412928), (-3440704061035/295147905179352825856)), (19085/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823625909477759/73786976294838206464), (-8596831028457/73786976294838206464)), (11937/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455705714046855/2305843009213693952), (-9664659291037/9223372036854775808)), (53767/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594066065888365/1152921504606846976), (-9656192670371/1152921504606846976)), (26915/576460752303423488), by norm_num⟩
  | 5 => ⟨((597322498106921/72057594037927936), (-8439647632581/144115188075855872)), (23587/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491721890506077/36028797018963968), (-3160109887399/9007199254740992)), (35451/18014398509481984), by norm_num⟩
  | 3 => ⟨((744671302730559/4503599627370496), (-7883633098065/4503599627370496)), (44439/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114028076037163/2251799813685248), (-15717386658173/2251799813685248)), (44627/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108056187492685/1125899906842624), (-23451540480277/1125899906842624)), (67411/562949953421312), by norm_num⟩
  | 0 => ⟨((1090071135201791/1125899906842624), (-46405884579471/1125899906842624)), (273425/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1090071135201791/1125899906842624), (-46405884579471/1125899906842624)), (1043033604148482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((526734910655921/562949953421312), (-44929140659977/562949953421312)), (137997/281474976710656), by norm_num⟩
  | 2 => ⟨((244631904443133/281474976710656), (-84077622700037/562949953421312)), (560533/562949953421312), by norm_num⟩
  | 3 => ⟨((825331014365129/1125899906842624), (-292289839793529/1125899906842624)), (1115/549755813888), by norm_num⟩
  | 4 => ⟨((132280393933303/281474976710656), (-428520987521733/1125899906842624)), (2266729/562949953421312), by norm_num⟩
  | 5 => ⟨((342266322518711/4503599627370496), (-1611082468516055/4503599627370496)), (30847733/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1100648676568251/9007199254740992), (-244879348697927/4503599627370496)), (13379605/2251799813685248), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-270018875/134217728), (-5425354245/134217728)), (1/67108864), by norm_num⟩, -6, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-273308947/134217728), (-2745730007/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1172318761350749/9007199254740992), (43373180329113/4503599627370496)), (12102425/2251799813685248), by norm_num⟩
  | 1 => ⟨((1821292733/4294967296), (-269535081/8589934592)), (303/17179869184), by norm_num⟩
  | 2 => ⟨((-1483486887/2147483648), (439085657/8589934592)), (31/1073741824), by norm_num⟩
  | 3 => ⟨((1611114497/2147483648), (-476861153/8589934592)), (271/8589934592), by norm_num⟩
  | 4 => ⟨((-5249166565/8589934592), (194207459/4294967296)), (111/4294967296), by norm_num⟩
  | 5 => ⟨((6840916565/17179869184), (-63274665/2147483648)), (291/17179869184), by norm_num⟩
  | 6 => ⟨((-3714727763/17179869184), (549746579/34359738368)), (159/17179869184), by norm_num⟩
  | 7 => ⟨((6915966665/68719476736), (-511750693/68719476736)), (149/34359738368), by norm_num⟩
  | 8 => ⟨((-2816610881/68719476736), (208416645/68719476736)), (61/34359738368), by norm_num⟩
  | 9 => ⟨((4078573405/274877906944), (-75449061/68719476736)), (89/137438953472), by norm_num⟩
  | 10 => ⟨((-1328838589/274877906944), (393312519/1099511627776)), (117/549755813888), by norm_num⟩
  | 11 => ⟨((787178983/549755813888), (-465981875/4398046511104)), (279/4398046511104), by norm_num⟩
  | 12 => ⟨((-1709803413/4398046511104), (506071311/17592186044416)), (305/17592186044416), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581323245535579/10141204801825835211973625643008), (999015770211/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778816171859511/633825300114114700748351602688), (4729431891783/633825300114114700748351602688)), (23167/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944897269799565/19807040628566084398385987584), (2659814553459/19807040628566084398385987584)), (13035/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944786040813147/1237940039285380274899124224), (5650927968625/2475880078570760549798248448)), (6927/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771237404354693/154742504910672534362390528), (5649602706245/154742504910672534362390528)), (13859/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774798119217377/4835703278458516698824704), (2647547278643/4835703278458516698824704)), (6499/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258825161637547/604462909807314587353088), (1157949970669/151115727451828646838272)), (22757/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471962369826697/18889465931478580854784), (470252209201/4722366482869645213696)), (36999/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162197614750651/590295810358705651712), (5640717247557/4722366482869645213696)), (13883/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202687814108079/73786976294838206464), (7752234164261/590295810358705651712)), (38207/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823538696593735/73786976294838206464), (9684665508003/73786976294838206464)), (47799/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455680896535931/2305843009213693952), (10887512734033/9223372036854775808)), (53831/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199245669266565/144115188075855872), (10877844940235/1152921504606846976)), (53903/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597277627622519/72057594037927936), (594202564845/9007199254740992)), (47245/144115188075855872), by norm_num⟩
  | 4 => ⟨((745792026020351/18014398509481984), (7119561242177/18014398509481984)), (71029/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489164681133433/9007199254740992), (17760876714525/9007199254740992)), (22267/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113841754345355/2251799813685248), (4425967845211/562949953421312)), (22373/562949953421312), by norm_num⟩
  | 1 => ⟨((1107755858354209/1125899906842624), (13206707444757/562949953421312)), (135299/1125899906842624), by norm_num⟩
  | 0 => ⟨((272346992427469/281474976710656), (13064499516377/281474976710656)), (68715/281474976710656), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((272346992427469/281474976710656), (13064499516377/281474976710656)), (262126923681163699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1051634557380147/1125899906842624), (25281658728143/281474976710656)), (557409/1125899906842624), by norm_num⟩
  | 2 => ⟨((486592386822425/562949953421312), (47228116504539/281474976710656)), (142677/140737488355328), by norm_num⟩
  | 3 => ⟨((25296450596377/35184372088832), (163288702986159/562949953421312)), (2356225/1125899906842624), by norm_num⟩
  | 4 => ⟨((974536825619645/2251799813685248), (939195299005371/2251799813685248)), (9509983/2251799813685248), by norm_num⟩
  | 5 => ⟨((60071250032069/4503599627370496), (812932303988123/2251799813685248)), (16164457/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1172318761350749/9007199254740992), (43373180329113/4503599627370496)), (12102425/2251799813685248), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-273308947/134217728), (-2745730007/67108864)), (1/67108864), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-276474835/134217728), (-2777535311/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-7657191280021/70368744177664), (74743748991117/1125899906842624)), (51778179/9007199254740992), by norm_num⟩
  | 1 => ⟨((1540335285/4294967296), (-1879449489/8589934592)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((-2538346909/4294967296), (3097179457/8589934592)), (17/536870912), by norm_num⟩
  | 3 => ⟨((2788659107/4294967296), (-850649853/2147483648)), (151/4294967296), by norm_num⟩
  | 4 => ⟨((-2297741373/4294967296), (2803603145/8589934592)), (251/8589934592), by norm_num⟩
  | 5 => ⟨((1514596145/4294967296), (-1848043721/8589934592)), (167/8589934592), by norm_num⟩
  | 6 => ⟨((-1663953937/8589934592), (1015141771/8589934592)), (185/17179869184), by norm_num⟩
  | 7 => ⟨((1566891637/17179869184), (-1911852385/34359738368)), (11/2147483648), by norm_num⟩
  | 8 => ⟨((-2582109611/68719476736), (1575288393/68719476736)), (73/34359738368), by norm_num⟩
  | 9 => ⟨((1891158233/137438953472), (-2307508249/274877906944)), (27/34359738368), by norm_num⟩
  | 10 => ⟨((-4986359219/1099511627776), (1521034151/549755813888)), (287/1099511627776), by norm_num⟩
  | 11 => ⟨((2988041189/2199023255552), (-911469169/1099511627776)), (173/2199023255552), by norm_num⟩
  | 12 => ⟨((-3282698769/8796093022208), (500675615/2199023255552)), (3/137438953472), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790646259958961/5070602400912917605986812821504), (3378708575475/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889391610674365/316912650057057350374175801344), (1999311541711/316912650057057350374175801344)), (11575/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889757671144565/39614081257132168796771975168), (2248810361643/19807040628566084398385987584)), (26049/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944766584424959/1237940039285380274899124224), (4777715618819/2475880078570760549798248448)), (6921/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771198783849257/154742504910672534362390528), (2388291754709/77371252455336267181195264)), (27693/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774780171031147/4835703278458516698824704), (1119211088785/2417851639229258349412352)), (25971/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314698515613383/151115727451828646838272), (3916036329417/604462909807314587353088)), (22733/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887799524203703/75557863725914323419136), (6361304815701/75557863725914323419136)), (36957/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648771979834983/2361183241434822606848), (4769006602761/4722366482869645213696)), (6933/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810726259903315/295147905179352825856), (3277090188401/295147905179352825856)), (38155/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823477440791313/73786976294838206464), (8187921341195/73786976294838206464)), (47729/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822656369835467/9223372036854775808), (9204808144983/9223372036854775808)), (53743/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796950127428273/576460752303423488), (9196557415493/1152921504606846976)), (13451/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194500670154681/144115188075855872), (8037710451983/144115188075855872)), (23573/72057594037927936), by norm_num⟩
  | 4 => ⟨((186438364468919/4503599627370496), (3009505770393/9007199254740992)), (70855/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489076530683147/9007199254740992), (7507553150565/4503599627370496)), (88807/9007199254740992), by norm_num⟩
  | 2 => ⟨((556882976960793/1125899906842624), (7483263286549/1125899906842624)), (89165/2251799813685248), by norm_num⟩
  | 1 => ⟨((553836420530747/562949953421312), (2791066298361/140737488355328)), (33661/281474976710656), by norm_num⟩
  | 0 => ⟨((136167939990069/140737488355328), (44173165968565/1125899906842624)), (136445/562949953421312), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((136167939990069/140737488355328), (44173165968565/1125899906842624)), (520496370555686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1052240992828157/1125899906842624), (85477850757043/1125899906842624)), (549473/1125899906842624), by norm_num⟩
  | 2 => ⟨((976911568544685/1125899906842624), (79885696764677/562949953421312)), (1110483/1125899906842624), by norm_num⟩
  | 3 => ⟨((1649932305564983/2251799813685248), (554516513280601/2251799813685248)), (2242237/1125899906842624), by norm_num⟩
  | 4 => ⟨((1072381316833895/2251799813685248), (203151875151279/562949953421312)), (8780349/2251799813685248), by norm_num⟩
  | 5 => ⟨((434914982831729/4503599627370496), (193495242399425/562949953421312)), (14700117/2251799813685248), by norm_num⟩
  | 6 => ⟨((-7657191280021/70368744177664), (74743748991117/1125899906842624)), (51778179/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-276474835/134217728), (-2777535311/67108864)), (1/67108864), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile031Terms3
