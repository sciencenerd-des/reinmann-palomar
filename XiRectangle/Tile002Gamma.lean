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
namespace Reinmann.XiRectangle.Tile002Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (141/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (141/128))
  have he : value ((3/4), (141/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((876544/11743657), (-36096/11743657)), 0, by norm_num⟩
  | 1 => ⟨((-383513231360/137913479733649), (31639732224/137913479733649)), 0, by norm_num⟩
  | 2 => ⟨((116449018453/1125899906842624), (-7225733461/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-69178483861/18014398509481984), (5746315783/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((20512570123/144115188075855872), (-17127017653/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((-48572579553/9223372036854775808), (12244411761/9223372036854775808)), (5/18446744073709551616), by norm_num⟩
  | 6 => ⟨((14351246425/73786976294838206464), (-17011452557/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-67718531485/9444732965739290427392), (23138791651/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((79734010813/302231454903657293676544), (-30963488939/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-93698527711/9671406556917033397649408), (40898931981/9671406556917033397649408)), (7/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((54943426515/154742504910672534362390528), (-6681369439/38685626227668133590597632)), (5/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-64301125969/4951760157141521099596496896), (34618579337/4951760157141521099596496896)), (13/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((75088261071/158456325028528675187087900672), (-5563125941/19807040628566084398385987584)), (17/158456325028528675187087900672), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (141/256)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (141/256)))⁻¹=value ((876544/11743657), (-36096/11743657)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((876544/11743657), (-36096/11743657))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5571076097/2147483648), (707065911/17179869184)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((438272/11743657), (-18048/11743657)), 0, by norm_num⟩
  | 2 => ⟨((-95878307840/137913479733649), (7909933056/137913479733649)), 0, by norm_num⟩
  | 3 => ⟨((77632678969/4503599627370496), (-9634311281/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-69178483861/144115188075855872), (5746315783/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((32820112197/2305843009213693952), (-6850807061/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-16190859851/36893488147419103232), (4081470587/36893488147419103232)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((65605697943/4722366482869645213696), (-19441660065/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-67718531485/151115727451828646838272), (23138791651/151115727451828646838272)), (7/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((35437338139/2417851639229258349412352), (-27523101279/4835703278458516698824704)), (5/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-74958822169/154742504910672534362390528), (32719145585/154742504910672534362390528)), (3/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((79917711295/4951760157141521099596496896), (-38873422191/4951760157141521099596496896)), (1/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-85734834625/158456325028528675187087900672), (46158105783/158456325028528675187087900672)), (9/79228162514264337593543950336), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (3/4096)), 0, by norm_num⟩
  | 45 => ⟨((21493764541/816127672320), (-5961/6029312)), 0, by norm_num⟩
  | 44 => ⟨((-10347345537227/383035920875520), (25339324861/23708219473920)), 0, by norm_num⟩
  | 43 => ⟨((60805218013/2199023255552), (-1215264185/1099511627776)), (1/4398046511104), by norm_num⟩
  | 42 => ⟨((-31124942275/1099511627776), (4983813869/4398046511104)), (1/4398046511104), by norm_num⟩
  | 41 => ⟨((31880902129/1099511627776), (-79740869/68719476736)), (1/4398046511104), by norm_num⟩
  | 40 => ⟨((-65348662849/2199023255552), (2613564953/2199023255552)), (1/4398046511104), by norm_num⟩
  | 39 => ⟨((67016507769/2199023255552), (-1339169569/1099511627776)), (1/2199023255552), by norm_num⟩
  | 38 => ⟨((-68771730161/2199023255552), (171648735/137438953472)), (1/2199023255552), by norm_num⟩
  | 37 => ⟨((17655345509/549755813888), (-704491037/549755813888)), (1/2199023255552), by norm_num⟩
  | 36 => ⟨((-36286647349/1099511627776), (180836285/137438953472)), (1/2199023255552), by norm_num⟩
  | 35 => ⟨((74636190799/2199023255552), (-2972945871/2199023255552)), (1/2199023255552), by norm_num⟩
  | 34 => ⟨((-38409907225/1099511627776), (191063271/137438953472)), (1/2199023255552), by norm_num⟩
  | 33 => ⟨((79135085091/2199023255552), (-393246647/274877906944)), (1/2199023255552), by norm_num⟩
  | 32 => ⟨((-40797140097/1099511627776), (405033599/274877906944)), (1/2199023255552), by norm_num⟩
  | 31 => ⟨((21052813297/549755813888), (-835098519/549755813888)), (1/2199023255552), by norm_num⟩
  | 30 => ⟨((-10875211845/274877906944), (3446907109/2199023255552)), (1/2199023255552), by norm_num⟩
  | 29 => ⟨((89983447931/2199023255552), (-3560439585/2199023255552)), (1/2199023255552), by norm_num⟩
  | 28 => ⟨((-93176890307/2199023255552), (3681709365/2199023255552)), (1/2199023255552), by norm_num⟩
  | 27 => ⟨((96605400797/2199023255552), (-952883925/549755813888)), (1/2199023255552), by norm_num⟩
  | 26 => ⟨((-195890495/4294967296), (3950857789/2199023255552)), (1/2199023255552), by norm_num⟩
  | 25 => ⟨((104279728153/2199023255552), (-1025189395/549755813888)), (1/2199023255552), by norm_num⟩
  | 24 => ⟨((-108593198107/2199023255552), (4262487979/2199023255552)), (1/2199023255552), by norm_num⟩
  | 23 => ⟨((56639523587/1099511627776), (-4437508021/2199023255552)), (1/2199023255552), by norm_num⟩
  | 22 => ⟨((-118387690189/2199023255552), (2313763555/1099511627776)), (1/2199023255552), by norm_num⟩
  | 21 => ⟨((123979076345/2199023255552), (-2417280583/1099511627776)), (1/2199023255552), by norm_num⟩
  | 20 => ⟨((-8132815993/137438953472), (2530502303/1099511627776)), (1/2199023255552), by norm_num⟩
  | 19 => ⟨((68456244455/1099511627776), (-2654861813/1099511627776)), (1/1099511627776), by norm_num⟩
  | 18 => ⟨((-18055922855/274877906944), (2792089259/1099511627776)), (1/1099511627776), by norm_num⟩
  | 17 => ⟨((19107559887/274877906944), (-736073271/274877906944)), (1/1099511627776), by norm_num⟩
  | 16 => ⟨((-81157459073/1099511627776), (1557034757/549755813888)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((86508472621/1099511627776), (-826163113/274877906944)), (1/1099511627776), by norm_num⟩
  | 14 => ⟨((-92615582343/1099511627776), (110003823/34359738368)), (1/1099511627776), by norm_num⟩
  | 13 => ⟨((99651385413/1099511627776), (-3765702959/1099511627776)), (1/1099511627776), by norm_num⟩
  | 12 => ⟨((-107845394489/1099511627776), (2024096403/549755813888)), (1/1099511627776), by norm_num⟩
  | 11 => ⟨((117509633265/1099511627776), (-1094151989/274877906944)), (1/1099511627776), by norm_num⟩
  | 10 => ⟨((-129079427385/1099511627776), (4763168661/1099511627776)), (1/1099511627776), by norm_num⟩
  | 9 => ⟨((71590542849/549755813888), (-2612432691/549755813888)), (1/549755813888), by norm_num⟩
  | 8 => ⟨((-40187435119/274877906944), (2893022781/549755813888)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((91623458071/549755813888), (-3241447269/549755813888)), (1/549755813888), by norm_num⟩
  | 6 => ⟨((-106546359547/549755813888), (3685830115/549755813888)), (1/274877906944), by norm_num⟩
  | 5 => ⟨((31826136127/137438953472), (-534055009/68719476736)), (1/274877906944), by norm_num⟩
  | 4 => ⟨((-79088890781/274877906944), (2541628479/274877906944)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((104513997543/274877906944), (-3139528305/274877906944)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((-38619426653/68719476736), (2056425375/137438953472)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((18755020351/17179869184), (-1498119649/68719476736)), (1/68719476736), by norm_num⟩
  | 0 => ⟨((-3064102773/17179869184), (22626109145/549755813888)), (3/549755813888), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (141/4096)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (141/4096)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (141/4096))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((5571076097/2147483648), (707065911/17179869184)), (1/34359738368), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (141/256))) (z:=((-21/128), (141/4096))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((5571076097/2147483648), (707065911/17179869184))) (r:=(1/34359738368)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((35839462459/1073741824), (4206378457/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((122214654227/68719476736), (733468443/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((1334668164096/137913479733649), (-56942346912/137913479733649)), 0, by norm_num⟩
  | 3 => ⟨((-35039879943/281474976710656), (5983412545/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((86279989453/36028797018963968), (-691930639/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-31773907569/576460752303423488), (10906807019/1152921504606846976)), (23/1152921504606846976), by norm_num⟩
  | 6 => ⟨((103711159045/73786976294838206464), (-22350289415/73786976294838206464)), (15/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-1412762247/36893488147419103232), (5879641569/590295810358705651712)), (37/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((82535330815/75557863725914323419136), (-3153294747/9444732965739290427392)), (3/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-77912919277/2417851639229258349412352), (27448590121/2417851639229258349412352)), (31/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((75439446559/77371252455336267181195264), (-30198267415/77371252455336267181195264)), (161/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-74494934857/2475880078570760549798248448), (8378524447/618970019642690137449562112)), (205/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((74712182861/79228162514264337593543950336), (-18727570621/39614081257132168796771975168)), (125/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((21478165563/1073741824), (3023584729/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((87854915859/68719476736), (733468443/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((1334668164096/137913479733649), (-56942346912/137913479733649)), 0, by norm_num⟩
  | 3 => ⟨((-35039879943/281474976710656), (5983412545/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((86279989453/36028797018963968), (-691930639/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-31773907569/576460752303423488), (10906807019/1152921504606846976)), (23/1152921504606846976), by norm_num⟩
  | 6 => ⟨((103711159045/73786976294838206464), (-22350289415/73786976294838206464)), (15/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-1412762247/36893488147419103232), (5879641569/590295810358705651712)), (37/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((82535330815/75557863725914323419136), (-3153294747/9444732965739290427392)), (3/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-77912919277/2417851639229258349412352), (27448590121/2417851639229258349412352)), (31/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((75439446559/77371252455336267181195264), (-30198267415/77371252455336267181195264)), (161/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-74494934857/2475880078570760549798248448), (8378524447/618970019642690137449562112)), (205/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((74712182861/79228162514264337593543950336), (-18727570621/39614081257132168796771975168)), (125/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((89859473199/4294967296), (3023584729/2147483648)), (3/4294967296), by norm_num⟩
  | 1 => ⟨((87854915859/68719476736), (733468443/34359738368)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((1334668164096/137913479733649), (-56942346912/137913479733649)), 0, by norm_num⟩
  | 3 => ⟨((-35039879943/281474976710656), (5983412545/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((86279989453/36028797018963968), (-691930639/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-31773907569/576460752303423488), (10906807019/1152921504606846976)), (23/1152921504606846976), by norm_num⟩
  | 6 => ⟨((103711159045/73786976294838206464), (-22350289415/73786976294838206464)), (15/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-1412762247/36893488147419103232), (5879641569/590295810358705651712)), (37/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((82535330815/75557863725914323419136), (-3153294747/9444732965739290427392)), (3/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-77912919277/2417851639229258349412352), (27448590121/2417851639229258349412352)), (31/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((75439446559/77371252455336267181195264), (-30198267415/77371252455336267181195264)), (161/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-74494934857/2475880078570760549798248448), (8378524447/618970019642690137449562112)), (205/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((74712182861/79228162514264337593543950336), (-18727570621/39614081257132168796771975168)), (125/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((767026462720/137913479733649), (-63279464448/137913479733649)), 0, by norm_num⟩
  | 1 => ⟨((-116449018453/281474976710656), (7225733461/140737488355328)), (1/281474976710656), by norm_num⟩
  | 2 => ⟨((3242741431/140737488355328), (-17238947349/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-20512570123/18014398509481984), (17127017653/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((60715724441/1152921504606846976), (-15305514701/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-86107478551/36893488147419103232), (6379294709/9223372036854775808)), (5/36893488147419103232), by norm_num⟩
  | 6 => ⟨((29626857525/295147905179352825856), (-20246442695/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-79734010813/18889465931478580854784), (30963488939/18889465931478580854784)), (1/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((52705421837/302231454903657293676544), (-23005649239/302231454903657293676544)), (7/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-8584910393/1208925819614629174706176), (16703423597/4835703278458516698824704)), (11/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((88414048207/309485009821345068724781056), (-11900136647/77371252455336267181195264)), (1/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-56316195803/4951760157141521099596496896), (16689377823/2475880078570760549798248448)), (3/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((17770279213/39614081257132168796771975168), (-46184317327/158456325028528675187087900672)), (17/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((116449018453/281474976710656), (-7225733461/140737488355328)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((-3242741431/70368744177664), (17238947349/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((61537710369/18014398509481984), (-1605657905/2251799813685248)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((-60715724441/288230376151711744), (15305514701/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((26908587047/2305843009213693952), (-15948236773/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-88880572575/147573952589676412928), (30369664043/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 6 => ⟨((69767259461/2361183241434822606848), (-13546526411/1180591620717411303424)), (3/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-52705421837/37778931862957161709568), (23005649239/37778931862957161709568)), (3/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((77264193537/1208925819614629174706176), (-18791351547/604462909807314587353088)), (5/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-27629390065/9671406556917033397649408), (29750341617/19342813113834066795298816)), (9/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((38717384615/309485009821345068724781056), (-11473947253/154742504910672534362390528)), (15/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-53310837639/9903520314283042199192993792), (34638237995/9903520314283042199192993792)), (3/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((72289339105/316912650057057350374175801344), (-6414916403/39614081257132168796771975168)), (19/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((69178483861/2251799813685248), (-5746315783/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-82050280493/18014398509481984), (17127017653/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((60715724441/144115188075855872), (-7652757351/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-35878116063/1152921504606846976), (21264315697/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((18516785953/9223372036854775808), (-25308053369/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-69767259461/590295810358705651712), (13546526411/295147905179352825856)), (3/295147905179352825856), by norm_num⟩
  | 6 => ⟨((30744829405/4722366482869645213696), (-26839924113/9444732965739290427392)), (3/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-25754731179/75557863725914323419136), (6263783849/37778931862957161709568)), (3/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((82888170195/4835703278458516698824704), (-22312756213/2417851639229258349412352)), (3/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-32264487179/38685626227668133590597632), (9561622711/19342813113834066795298816)), (11/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((12217066959/309485009821345068724781056), (-15875859081/618970019642690137449562112)), (5/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-72289339105/39614081257132168796771975168), (6414916403/4951760157141521099596496896)), (17/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((52379223845/633825300114114700748351602688), (-40526564981/633825300114114700748351602688)), (15/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((20512570123/9007199254740992), (-17127017653/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 1 => ⟨((-30357862221/72057594037927936), (7652757351/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 2 => ⟨((26908587047/576460752303423488), (-15948236773/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-18516785953/4611686018427387904), (25308053369/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 4 => ⟨((87209074327/295147905179352825856), (-8466579007/73786976294838206464)), (7/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-92234488215/4722366482869645213696), (40259886169/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((45070779563/37778931862957161709568), (-43846486943/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-82888170195/1208925819614629174706176), (44625512427/1208925819614629174706176)), (11/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((72595096153/19342813113834066795298816), (-5378412775/2417851639229258349412352)), (11/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-61085334795/309485009821345068724781056), (39689647703/309485009821345068724781056)), (11/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((49698920635/4951760157141521099596496896), (-35282040217/4951760157141521099596496896)), (11/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-9821104471/19807040628566084398385987584), (3799365467/9903520314283042199192993792)), (5/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((3785009005/158456325028528675187087900672), (-50974237873/2535301200456458802993406410752)), (9/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((48572579553/288230376151711744), (-12244411761/288230376151711744)), (5/576460752303423488), by norm_num⟩
  | 1 => ⟨((-10763434819/288230376151711744), (25517178837/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 2 => ⟨((88880572575/18446744073709551616), (-30369664043/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-69767259461/147573952589676412928), (13546526411/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 4 => ⟨((92234488215/2361183241434822606848), (-40259886169/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-13521233869/4722366482869645213696), (13153946083/9444732965739290427392)), (3/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1813178723/9444732965739290427392), (-31237858699/302231454903657293676544)), (1/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-29038038461/2417851639229258349412352), (1075682555/151115727451828646838272)), (9/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((54976801315/77371252455336267181195264), (-35720682933/77371252455336267181195264)), (5/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-49698920635/1237940039285380274899124224), (35282040217/1237940039285380274899124224)), (5/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((5401607459/2475880078570760549798248448), (-16717208055/9903520314283042199192993792)), (11/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-2271005403/19807040628566084398385987584), (61169085449/633825300114114700748351602688)), (5/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((59343851907/10141204801825835211973625643008), (-54275522693/10141204801825835211973625643008)), (19/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((14351246425/1152921504606846976), (-17011452557/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-59253715051/18446744073709551616), (2530805337/2305843009213693952)), (5/18446744073709551616), by norm_num⟩
  | 2 => ⟨((34883629731/73786976294838206464), (-27093052823/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-30744829405/590295810358705651712), (26839924113/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 4 => ⟨((45070779563/9444732965739290427392), (-43846486943/18889465931478580854784)), (9/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-58021719137/151115727451828646838272), (31237858699/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((16938855769/604462909807314587353088), (-40158815387/2417851639229258349412352)), (5/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-36651200877/19342813113834066795298816), (11906894311/9671406556917033397649408)), (13/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((9318547619/77371252455336267181195264), (-26461530163/309485009821345068724781056)), (15/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-72021432787/9903520314283042199192993792), (27862013425/4951760157141521099596496896)), (1/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((8327019811/19807040628566084398385987584), (-28035830831/79228162514264337593543950336)), (9/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-59343851907/2535301200456458802993406410752), (54275522693/2535301200456458802993406410752)), (9/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((51151052581/40564819207303340847894502572032), (-25401095813/20282409603651670423947251286016)), (9/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((67718531485/73786976294838206464), (-23138791651/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 1 => ⟨((-39867005407/147573952589676412928), (30963488941/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 2 => ⟨((26352710919/590295810358705651712), (-2875706155/147573952589676412928)), (3/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-25754731179/4722366482869645213696), (25055135397/9444732965739290427392)), (3/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((82888170195/151115727451828646838272), (-44625512427/151115727451828646838272)), (5/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-58076076923/1208925819614629174706176), (1075682555/37778931862957161709568)), (9/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((36651200877/9671406556917033397649408), (-11906894311/4835703278458516698824704)), (3/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-21299537415/77371252455336267181195264), (15120874379/77371252455336267181195264)), (9/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((23149746253/1237940039285380274899124224), (-17911294345/1237940039285380274899124224)), (11/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-47582970349/39614081257132168796771975168), (40051186901/39614081257132168796771975168)), (3/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((11656828053/158456325028528675187087900672), (-42645053545/633825300114114700748351602688)), (7/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-43843759355/10141204801825835211973625643008), (43544735679/10141204801825835211973625643008)), (15/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((1242381091/5070602400912917605986812821504), (-42875784573/162259276829213363391578010288128)), (1/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((79734010813/1180591620717411303424), (-30963488939/1180591620717411303424)), (5/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-26352710919/1180591620717411303424), (2875706155/295147905179352825856)), (7/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((38632096769/9444732965739290427392), (-37582703095/18889465931478580854784)), (5/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-82888170195/151115727451828646838272), (11156378107/37778931862957161709568)), (11/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((72595096153/1208925819614629174706176), (-5378412775/151115727451828646838272)), (11/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-13744200329/2417851639229258349412352), (35720682933/9671406556917033397649408)), (9/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((9318547619/19342813113834066795298816), (-26461530163/77371252455336267181195264)), (7/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-23149746253/618970019642690137449562112), (17911294345/618970019642690137449562112)), (11/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((26765420821/9903520314283042199192993792), (-2816099079/1237940039285380274899124224)), (7/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-29142070133/158456325028528675187087900672), (53306316931/316912650057057350374175801344)), (17/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((30142584557/2535301200456458802993406410752), (-7484251445/633825300114114700748351602688)), (5/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((-59634292367/81129638414606681695789005144064), (16078419215/20282409603651670423947251286016)), (23/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((56712163499/1298074214633706907132624082305024), (-66448724319/1298074214633706907132624082305024)), (25/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((93698527711/18889465931478580854784), (-40898931981/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-68679283145/37778931862957161709568), (8351711799/9444732965739290427392)), (11/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((55258780131/151115727451828646838272), (-14875170809/75557863725914323419136)), (9/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-64528974359/1208925819614629174706176), (38246490845/1208925819614629174706176)), (5/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((61085334795/9671406556917033397649408), (-4961205963/1208925819614629174706176)), (11/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-49698920635/77371252455336267181195264), (17641020109/38685626227668133590597632)), (5/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((18005358197/309485009821345068724781056), (-27862013425/618970019642690137449562112)), (1/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-47582970349/9903520314283042199192993792), (20025593451/4951760157141521099596496896)), (13/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((29142070133/79228162514264337593543950336), (-53306316931/158456325028528675187087900672)), (17/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((-33491760619/1267650600228229401496703205376), (66526679511/2535301200456458802993406410752)), (11/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((36443178669/20282409603651670423947251286016), (-19651401263/10141204801825835211973625643008)), (7/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((-37808108999/324518553658426726783156020576256), (22149574773/162259276829213363391578010288128)), (1/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((37601599391/5192296858534827628530496329220096), (-11979408403/1298074214633706907132624082305024)), (19/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((54943426515/151115727451828646838272), (-6681369439/37778931862957161709568)), (5/75557863725914323419136), by norm_num⟩
  | 1 => ⟨((-88414048209/604462909807314587353088), (23800273295/302231454903657293676544)), (1/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((4839673077/151115727451828646838272), (-22947894507/1208925819614629174706176)), (15/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((-48868267837/9671406556917033397649408), (31751718163/9671406556917033397649408)), (9/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((49698920635/77371252455336267181195264), (-17641020109/38685626227668133590597632)), (5/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-43212859673/618970019642690137449562112), (33434416111/618970019642690137449562112)), (5/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((66616158489/9903520314283042199192993792), (-28035830831/4951760157141521099596496896)), (17/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((-46627312213/79228162514264337593543950336), (42645053545/79228162514264337593543950336)), (7/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((30142584557/633825300114114700748351602688), (-7484251445/158456325028528675187087900672)), (5/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((-18221589335/5070602400912917605986812821504), (19651401263/5070602400912917605986812821504)), (7/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((41588919899/162259276829213363391578010288128), (-48729064501/162259276829213363391578010288128)), (9/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((-45121919269/2596148429267413814265248164610048), (28750580167/1298074214633706907132624082305024)), (11/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((46803551673/41538374868278621028243970633760768), (-64981597777/41538374868278621028243970633760768)), (13/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((219136/35230971), (-3008/11743657)), 0, by norm_num⟩
  | 1 => ⟨((-95878307840/413740439200947), (2636644352/137913479733649)), 0, by norm_num⟩
  | 2 => ⟨((77632678969/9007199254740992), (-9634311281/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-92237978481/288230376151711744), (15323508755/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((109400373989/9223372036854775808), (-22836023537/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-16190859851/36893488147419103232), (4081470587/36893488147419103232)), (1/36893488147419103232), by norm_num⟩
  | 6 => ⟨((76539980933/4722366482869645213696), (-22681936743/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-90291375313/151115727451828646838272), (30851722201/151115727451828646838272)), (5/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((53156007209/2417851639229258349412352), (-20642325959/2417851639229258349412352)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-62465685141/77371252455336267181195264), (13632977327/38685626227668133590597632)), (5/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((18314475505/618970019642690137449562112), (-35633970341/2475880078570760549798248448)), (7/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-85734834625/79228162514264337593543950336), (46158105783/79228162514264337593543950336)), (9/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((25029420357/633825300114114700748351602688), (-29670005019/1267650600228229401496703205376)), (3/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44943093909/2147483648), (6046069353/4294967296)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((87838991123/68719476736), (91765667/4294967296)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((10650083847/1099511627776), (-3641179537/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-17564978047/140737488355328), (6013341273/562949953421312)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((10838416833/4503599627370496), (-11160093441/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-16013444877/288230376151711744), (11034352975/1152921504606846976)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((104907096247/73786976294838206464), (-22704694677/73786976294838206464)), (61/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-91827586547/2361183241434822606848), (24000624435/2361183241434822606848)), (75/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((10524557005/9444732965739290427392), (-12935715331/37778931862957161709568)), (97/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-39932485969/1208925819614629174706176), (7075162801/604462909807314587353088)), (125/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((77728755997/77371252455336267181195264), (-7827957247/19342813113834066795298816)), (81/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-77174148439/2475880078570760549798248448), (17478269297/1237940039285380274899124224)), (103/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((38920430203/39614081257132168796771975168), (-9827379139/19807040628566084398385987584)), (63/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-20702047725/18014398509481984), (2569149675/18014398509481984)), (1/72057594037927936), by norm_num⟩
  | 1 => ⟨((73790382785/576460752303423488), (-3064701751/144115188075855872)), (3/576460752303423488), by norm_num⟩
  | 2 => ⟨((-87520299191/9223372036854775808), (9134409415/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((43175626269/73786976294838206464), (-10883921565/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-38269990467/1180591620717411303424), (2835242093/295147905179352825856)), (5/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((1975123835/1180591620717411303424), (-10798102771/18889465931478580854784)), (5/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-24806136697/302231454903657293676544), (1204135681/37778931862957161709568)), (3/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((9369852771/2417851639229258349412352), (-2044946599/1208925819614629174706176)), (5/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-54943426515/309485009821345068724781056), (6681369439/77371252455336267181195264)), (1/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((39295132537/4951760157141521099596496896), (-21155798483/4951760157141521099596496896)), (7/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-27532362393/79228162514264337593543950336), (2039812845/9903520314283042199192993792)), (3/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((75819857975/5070602400912917605986812821504), (-49263271815/5070602400912917605986812821504)), (9/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-12851438063/20282409603651670423947251286016), (4561718331/10141204801825835211973625643008)), (15/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44943091441/2147483648), (3023034983/2147483648)), (5/4294967296), by norm_num⟩
  | 1 => ⟨((87838999919/68719476736), (1468249211/68719476736)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((42600293655/4398046511104), (-1820581057/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-1097805981/8796093022208), (6013258235/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((86706166757/36028797018963968), (-5579873671/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-16012962669/288230376151711744), (11033693911/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((104901040061/73786976294838206464), (-22702342849/73786976294838206464)), (31/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-22954609075/590295810358705651712), (23996630399/2361183241434822606848)), (19/590295810358705651712), by norm_num⟩
  | 8 => ⟨((42091521059/37778931862957161709568), (-25864905887/75557863725914323419136)), (49/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-39922892431/1208925819614629174706176), (3536290153/302231454903657293676544)), (63/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((19425467231/19342813113834066795298816), (-15647946475/38685626227668133590597632)), (163/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-4821070439/154742504910672534362390528), (17466242131/1237940039285380274899124224)), (207/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((19447664869/19807040628566084398385987584), (-9818469533/19807040628566084398385987584)), (253/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((66682132717/36893488147419103232), (-13919100061/36893488147419103232)), (3/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-3083973305/9223372036854775808), (777422969/9223372036854775808)), (3/147573952589676412928), by norm_num⟩
  | 2 => ⟨((21868565981/590295810358705651712), (-12961106711/1180591620717411303424)), (3/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-60194250209/18889465931478580854784), (20567814801/18889465931478580854784)), (5/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((35437338139/151115727451828646838272), (-860096915/9444732965739290427392)), (7/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((-9369852771/604462909807314587353088), (32719145585/4835703278458516698824704)), (1/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((18314475505/19342813113834066795298816), (-35633970341/77371252455336267181195264)), (9/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-67363084349/1237940039285380274899124224), (36267083115/1237940039285380274899124224)), (5/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((58997919413/19807040628566084398385987584), (-34968220201/19807040628566084398385987584)), (5/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-49643954627/316912650057057350374175801344), (32255713689/316912650057057350374175801344)), (5/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((40390233913/5070602400912917605986812821504), (-28673658081/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-15963192029/40564819207303340847894502572032), (49403812549/162259276829213363391578010288128)), (17/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((49217132967/2596148429267413814265248164610048), (-1294583819/81129638414606681695789005144064)), (1/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44943091445/2147483648), (1511517491/1073741824)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((10979874987/8589934592), (1468249217/68719476736)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((21300146909/2199023255552), (-3641162211/8796093022208)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-35129792289/281474976710656), (187914339/17592186044416)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((43353087603/18014398509481984), (-11159750623/36028797018963968)), (19/36028797018963968), by norm_num⟩
  | 5 => ⟨((-16012967137/288230376151711744), (689606357/72057594037927936)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((104901109925/73786976294838206464), (-177362319/576460752303423488)), (63/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-91818564785/2361183241434822606848), (23996699573/2361183241434822606848)), (77/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((84183267177/75557863725914323419136), (-1616564955/4722366482869645213696)), (99/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-79846163615/2417851639229258349412352), (7072641829/604462909807314587353088)), (127/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((38851242615/38685626227668133590597632), (-31296330475/77371252455336267181195264)), (41/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-19284525335/618970019642690137449562112), (4366654763/309485009821345068724781056)), (13/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((9724020183/9903520314283042199192993792), (-19637571187/39614081257132168796771975168)), (127/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-69979411139/9444732965739290427392), (1296110671/590295810358705651712)), (7/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((72233100253/37778931862957161709568), (-24681377763/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-85049611535/302231454903657293676544), (33027721537/302231454903657293676544)), (9/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((9369852771/302231454903657293676544), (-32719145585/2417851639229258349412352)), (9/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((-54943426515/19342813113834066795298816), (6681369439/4835703278458516698824704)), (3/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((70731238567/309485009821345068724781056), (-38080437271/309485009821345068724781056)), (5/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((-41298543589/2475880078570760549798248448), (48955508281/4951760157141521099596496896)), (13/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((11169889791/9903520314283042199192993792), (-1814383895/2475880078570760549798248448)), (9/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((-1419969161/19807040628566084398385987584), (16128932671/316912650057057350374175801344)), (5/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((1371836815/316912650057057350374175801344), (-4245640141/1267650600228229401496703205376)), (11/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((-40604134697/162259276829213363391578010288128), (34177012823/162259276829213363391578010288128)), (3/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((18085745343/1298074214633706907132624082305024), (-8270555839/649037107316853453566312041152512)), (3/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-62355568861/83076749736557242056487941267521536), (7741286343/10384593717069655257060992658440192)), (23/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44943091445/2147483648), (1511517491/1073741824)), (7/4294967296), by norm_num⟩
  | 1 => ⟨((10979874987/8589934592), (1468249217/68719476736)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((42600293817/4398046511104), (-1820581105/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-70259584561/562949953421312), (751657355/70368744177664)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((677391993/281474976710656), (-11159750573/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-64051868285/1152921504606846976), (5516850785/576460752303423488)), (27/1152921504606846976), by norm_num⟩
  | 6 => ⟨((52450554347/36893488147419103232), (-22702376103/73786976294838206464)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-45909281061/1180591620717411303424), (23996697843/2361183241434822606848)), (39/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((1315363465/1180591620717411303424), (-25865035435/75557863725914323419136)), (25/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-79846153149/2417851639229258349412352), (14145279609/1208925819614629174706176)), (1/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((19425616467/19342813113834066795298816), (-15648157089/38685626227668133590597632)), (165/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-19284516711/618970019642690137449562112), (17466603277/1237940039285380274899124224)), (209/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((77792101997/79228162514264337593543950336), (-39275083313/79228162514264337593543950336)), (255/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((68726958815/1208925819614629174706176), (-26689067907/1208925819614629174706176)), (9/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((-90859178387/4835703278458516698824704), (39659570407/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 2 => ⟨((66598092747/19342813113834066795298816), (-32394518493/19342813113834066795298816)), (5/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((-35722847761/77371252455336267181195264), (38465088153/154742504910672534362390528)), (11/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((62573550893/1237940039285380274899124224), (-37087506273/1237940039285380274899124224)), (11/1237940039285380274899124224), by norm_num⟩
  | 5 => ⟨((-47387411235/9903520314283042199192993792), (30789544885/9903520314283042199192993792)), (9/9903520314283042199192993792), by norm_num⟩
  | 6 => ⟨((16064297579/39614081257132168796771975168), (-45617183311/158456325028528675187087900672)), (13/158456325028528675187087900672), by norm_num⟩
  | 7 => ⟨((-39907980073/1267650600228229401496703205376), (7719345711/316912650057057350374175801344)), (11/1267650600228229401496703205376), by norm_num⟩
  | 8 => ⟨((11535265539/5070602400912917605986812821504), (-38837514571/20282409603651670423947251286016)), (13/20282409603651670423947251286016), by norm_num⟩
  | 9 => ⟨((-50238181509/324518553658426726783156020576256), (45947532439/324518553658426726783156020576256)), (1/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((51962974051/5192296858534827628530496329220096), (-51608575621/5192296858534827628530496329220096)), (9/2596148429267413814265248164610048), by norm_num⟩
  | 11 => ⟨((-3212621811/5192296858534827628530496329220096), (6929419729/10384593717069655257060992658440192)), (21/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((12220802909/332306998946228968225951765070086144), (-14318917025/332306998946228968225951765070086144)), (23/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44943091445/2147483648), (1511517491/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((10979874987/8589934592), (1468249217/68719476736)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((42600293817/4398046511104), (-1820581105/4398046511104)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((-70259584561/562949953421312), (751657355/70368744177664)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((43353087553/18014398509481984), (-5579875287/18014398509481984)), (21/36028797018963968), by norm_num⟩
  | 5 => ⟨((-64051868291/1152921504606846976), (5516850787/576460752303423488)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((26225277181/18446744073709551616), (-5675594031/18446744073709551616)), (65/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-22954640549/590295810358705651712), (23996697901/2361183241434822606848)), (79/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((21045815483/18889465931478580854784), (-6466258895/18889465931478580854784)), (101/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-79846153523/2417851639229258349412352), (3536319945/302231454903657293676544)), (129/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((38851233321/38685626227668133590597632), (-31296314947/77371252455336267181195264)), (83/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-9642258547/309485009821345068724781056), (17466604103/1237940039285380274899124224)), (105/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((77792104911/79228162514264337593543950336), (-39275086727/79228162514264337593543950336)), (1/309485009821345068724781056), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-53942015633/77371252455336267181195264), (13119186683/38685626227668133590597632)), (11/77371252455336267181195264), by norm_num⟩
  | 1 => ⟨((10850324309/38685626227668133590597632), (-730202635/4835703278458516698824704)), (1/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((-38011713115/618970019642690137449562112), (11264820587/309485009821345068724781056)), (1/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((47977584123/4951760157141521099596496896), (-31173004419/4951760157141521099596496896)), (5/2475880078570760549798248448), by norm_num⟩
  | 4 => ⟨((-24396548631/19807040628566084398385987584), (17319491027/19807040628566084398385987584)), (11/39614081257132168796771975168), by norm_num⟩
  | 5 => ⟨((21212626331/158456325028528675187087900672), (-32825033147/316912650057057350374175801344)), (11/316912650057057350374175801344), by norm_num⟩
  | 6 => ⟨((-65401997847/5070602400912917605986812821504), (6881210915/633825300114114700748351602688)), (17/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((45777472645/40564819207303340847894502572032), (-41867795493/40564819207303340847894502572032)), (15/40564819207303340847894502572032), by norm_num⟩
  | 8 => ⟨((-29593199233/324518553658426726783156020576256), (58782734759/649037107316853453566312041152512)), (5/162259276829213363391578010288128), by norm_num⟩
  | 9 => ⟨((35778957343/5192296858534827628530496329220096), (-19293230535/2596148429267413814265248164610048)), (15/5192296858534827628530496329220096), by norm_num⟩
  | 10 => ⟨((-40830911169/83076749736557242056487941267521536), (47840917937/83076749736557242056487941267521536)), (19/83076749736557242056487941267521536), by norm_num⟩
  | 11 => ⟨((22149758661/664613997892457936451903530140172288), (-56453131637/1329227995784915872903807060280344576)), (23/1329227995784915872903807060280344576), by norm_num⟩
  | 12 => ⟨((-22975249963/10633823966279326983230456482242756608), (63797228995/21267647932558653966460912964485513216)), (27/21267647932558653966460912964485513216), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44943091445/2147483648), (1511517491/1073741824)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((10979874987/8589934592), (1468249217/68719476736)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((42600293817/4398046511104), (-1820581105/4398046511104)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-70259584561/562949953421312), (751657355/70368744177664)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((43353087553/18014398509481984), (-5579875287/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-64051868291/1152921504606846976), (5516850787/576460752303423488)), (29/1152921504606846976), by norm_num⟩
  | 6 => ⟨((104901108723/73786976294838206464), (-22702376123/73786976294838206464)), (33/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-91818562193/2361183241434822606848), (23996697899/2361183241434822606848)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((84183261925/75557863725914323419136), (-25865035573/75557863725914323419136)), (51/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-39923076753/1208925819614629174706176), (14145279771/1208925819614629174706176)), (65/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((19425616651/19342813113834066795298816), (-15648157451/38685626227668133590597632)), (167/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-77138068293/2475880078570760549798248448), (34933208101/2475880078570760549798248448)), (211/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((19448026185/19807040628566084398385987584), (-39275086489/79228162514264337593543950336)), (257/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((104492838267923/524288), (635031906964527/524288)), (3340391/524288), by norm_num⟩
  | 1 => ⟨((14648125041/64), 1552480065), (541/64), by norm_num⟩
  | 2 => ⟨((8456004441/64), (64403499947/64)), (363/64), by norm_num⟩
  | 3 => ⟨((13055220987/256), (28128982779/64)), (41/16), by norm_num⟩
  | 4 => ⟨((3779563533/256), (74459135779/512)), (225/256), by norm_num⟩
  | 5 => ⟨((6978984173/2048), (79593173109/2048)), (499/2048), by norm_num⟩
  | 6 => ⟨((332892057/512), (71544601823/8192)), (233/4096), by norm_num⟩
  | 7 => ⟨((1716660857/16384), (27799511435/16384)), (753/65536), by norm_num⟩
  | 8 => ⟨((1888590477/131072), (19059035919/65536)), (539/262144), by norm_num⟩
  | 9 => ⟨((3538684805/2097152), (93650977711/2097152)), (693/2097152), by norm_num⟩
  | 10 => ⟨((2757595053/16777216), (52160819515/8388608)), (405/8388608), by norm_num⟩
  | 11 => ⟨((822315047/67108864), (53204897699/67108864)), (435/67108864), by norm_num⟩
  | 12 => ⟨((483183987/1073741824), (50094250511/536870912)), (433/536870912), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1611237159565281/10141204801825835211973625643008), (114606244829/633825300114114700748351602688)), (2731/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((113431267643319/39614081257132168796771975168), (1126236029615/316912650057057350374175801344)), (3361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((965217709536271/19807040628566084398385987584), (1270505003947/19807040628566084398385987584)), (3793/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1932796300861295/2475880078570760549798248448), (1352867604395/1237940039285380274899124224)), (4039/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1814510198394321/154742504910672534362390528), (2712347366241/154742504910672534362390528)), (2025/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((795108099465285/4835703278458516698824704), (2549872570241/9671406556917033397649408)), (119/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1294419466211885/604462909807314587353088), (559552785763/151115727451828646838272)), (209/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((972893842553283/37778931862957161709568), (3650409285743/75557863725914323419136)), (2727/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((83820007127889/295147905179352825856), (1374756929627/2361183241434822606848)), (4109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1681508408639293/590295810358705651712), (1899854702347/295147905179352825856)), (355/36893488147419103232), by norm_num⟩
  | 8 => ⟨((474689047543197/18446744073709551616), (2389255964355/36893488147419103232)), (3573/36893488147419103232), by norm_num⟩
  | 7 => ⟨((476908402871243/2305843009213693952), (5415829476773/9223372036854775808)), (1013/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1679240461501539/1152921504606846976), (2733144019559/576460752303423488)), (1023/144115188075855872), by norm_num⟩
  | 5 => ⟨((317396167719649/36028797018963968), (4840398597949/144115188075855872)), (7253/144115188075855872), by norm_num⟩
  | 4 => ⟨((802481542259343/18014398509481984), (7376986740373/36028797018963968)), (5533/18014398509481984), by norm_num⟩
  | 3 => ⟨((1632366659228831/9007199254740992), (2357139300775/2251799813685248)), (3541/2251799813685248), by norm_num⟩
  | 2 => ⟨((1259295678795617/2251799813685248), (9746963811035/2251799813685248)), (14675/2251799813685248), by norm_num⟩
  | 1 => ⟨((1331690092255233/1125899906842624), (15443051144943/1125899906842624)), (23337/1125899906842624), by norm_num⟩
  | 0 => ⟨((780514127179995/562949953421312), (268289806733/8796093022208)), (52253/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((780514127179995/562949953421312), (268289806733/8796093022208)), (199329380515670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1081636957816563/562949953421312), (11903238392591/140737488355328)), (37021/281474976710656), by norm_num⟩
  | 2 => ⟨((1037100641069855/281474976710656), (45741126666341/140737488355328)), (74263/140737488355328), by norm_num⟩
  | 3 => ⟨((1895743539095703/140737488355328), (337068341515019/140737488355328)), (9305/2199023255552), by norm_num⟩
  | 4 => ⟨((1545531924294703/8796093022208), (567541685346385/8796093022208)), (590499/4398046511104), by norm_num⟩
  | 5 => ⟨((114717422472947/4294967296), (779069069763645/34359738368)), (1108241/17179869184), by norm_num⟩
  | 6 => ⟨((104492838267923/524288), (635031906964527/524288)), (3340391/524288), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((44943091445/2147483648), (1511517491/1073741824)), (9/4294967296), by norm_num⟩, 0, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((90112/143785), (-36096/143785)), 0, by norm_num⟩
  | 1 => ⟨((-3408625664/20674126225), (3252682752/20674126225)), 0, by norm_num⟩
  | 2 => ⟨((94874619609088/2972629239261625), (-208071750057984/2972629239261625)), 0, by norm_num⟩
  | 3 => ⟨((-83506581/68719476736), (114084464223/4398046511104)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((-25290512493/8796093022208), (-18209986207/2199023255552)), (1/4398046511104), by norm_num⟩
  | 5 => ⟨((34135753453/17592186044416), (19650404317/8796093022208)), (3/17592186044416), by norm_num⟩
  | 6 => ⟨((-62518941525/70368744177664), (-32121713823/70368744177664)), (7/70368744177664), by norm_num⟩
  | 7 => ⟨((11811336789/35184372088832), (4436263607/140737488355328)), (13/281474976710656), by norm_num⟩
  | 8 => ⟨((-61445965769/562949953421312), (4540137931/140737488355328)), (13/562949953421312), by norm_num⟩
  | 9 => ⟨((67899928259/2251799813685248), (-26806949385/1125899906842624)), (3/281474976710656), by norm_num⟩
  | 10 => ⟨((-29094488613/4503599627370496), (50646252783/4503599627370496)), (11/2251799813685248), by norm_num⟩
  | 11 => ⟨((1379899533/2251799813685248), (-2440288361/562949953421312)), (5/2251799813685248), by norm_num⟩
  | 12 => ⟨((25370444817/72057594037927936), (103421738033/72057594037927936)), (9/9007199254740992), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (141/256)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (141/256)))⁻¹=value ((90112/143785), (-36096/143785)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((90112/143785), (-36096/143785))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((155648/389545), (-36096/389545)), 0, by norm_num⟩
  | 1 => ⟨((-11461689344/151745307025), (5618270208/151745307025)), 0, by norm_num⟩
  | 2 => ⟨((790595970793472/59111625625053625), (-644096829947904/59111625625053625)), 0, by norm_num⟩
  | 3 => ⟨((-38125289709/17592186044416), (49197216031/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((42699070791/140737488355328), (-92760720719/140737488355328)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((-2116401183/70368744177664), (41020386137/281474976710656)), (1/140737488355328), by norm_num⟩
  | 6 => ⟨((-1673926377/2251799813685248), (-68698769383/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 7 => ⟨((28138408373/18014398509481984), (109177671493/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 8 => ⟨((-42719399385/72057594037927936), (-5127007863/4503599627370496)), (3/18014398509481984), by norm_num⟩
  | 9 => ⟨((6167593403/36028797018963968), (28818588039/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 10 => ⟨((-50111078985/1152921504606846976), (-18457707249/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 11 => ⟨((93772868589/9223372036854775808), (40426661143/9223372036854775808)), (29/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-1287944927/576460752303423488), (-14927689941/36893488147419103232)), (15/18446744073709551616), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (141/256)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (141/256)))⁻¹=value ((155648/389545), (-36096/389545)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((155648/389545), (-36096/389545))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2544566272/11202145565), (-1774190592/11202145565)), 0, by norm_num⟩
  | 1 => ⟨((-49116050421/549755813888), (66139332289/549755813888)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((20386523069/1099511627776), (-32490339497/549755813888)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((1046725311/1099511627776), (101785160215/4398046511104)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((-13979602209/4398046511104), (-67042399783/8796093022208)), (1/4398046511104), by norm_num⟩
  | 5 => ⟨((34664853749/17592186044416), (9184258625/4398046511104)), (3/17592186044416), by norm_num⟩
  | 6 => ⟨((-31233315663/35184372088832), (-29974877279/70368744177664)), (7/70368744177664), by norm_num⟩
  | 7 => ⟨((47025515841/140737488355328), (447914131/17592186044416)), (13/281474976710656), by norm_num⟩
  | 8 => ⟨((-30556110231/281474976710656), (18801427707/562949953421312)), (13/562949953421312), by norm_num⟩
  | 9 => ⟨((67514453671/2251799813685248), (-6758023651/281474976710656)), (3/281474976710656), by norm_num⟩
  | 10 => ⟨((-28898742211/4503599627370496), (50790453621/4503599627370496)), (11/2251799813685248), by norm_num⟩
  | 11 => ⟨((5428023065/9007199254740992), (-39084092937/9007199254740992)), (5/2251799813685248), by norm_num⟩
  | 12 => ⟨((6382859483/18014398509481984), (103450893677/72057594037927936)), (71/72057594037927936), by norm_num⟩
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
  | 0 => ⟨((27/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((24576/85153), (-12032/255459)), 0, by norm_num⟩
  | 1 => ⟨((-2645524480/65259300681), (98566144/7251033409)), 0, by norm_num⟩
  | 2 => ⟨((3414364782592/617447247876577), (-48617356263424/16671075692667579)), 0, by norm_num⟩
  | 3 => ⟨((-51320012387/70368744177664), (38777252115/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((12985073831/140737488355328), (-54434592369/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-49706560791/4503599627370496), (72626907011/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((43700450857/36028797018963968), (-93208005035/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 7 => ⟨((-16444659411/144115188075855872), (57918050411/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 8 => ⟨((252272315/36028797018963968), (-69961037391/1152921504606846976)), (9/1152921504606846976), by norm_num⟩
  | 9 => ⟨((965266983/2305843009213693952), (20571670055/2305843009213693952)), (13/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-9980013645/36893488147419103232), (-47133794385/36893488147419103232)), (9/36893488147419103232), by norm_num⟩
  | 11 => ⟨((20401242627/295147905179352825856), (26266452685/147573952589676412928)), (13/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-16724552541/1180591620717411303424), (-28401256529/1180591620717411303424)), (19/2361183241434822606848), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (141/256)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (141/256)))⁻¹=value ((24576/85153), (-12032/255459)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((24576/85153), (-12032/255459))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((55419573633024/953896301296445), (-32284749070336/572337780777867)), 0, by norm_num⟩
  | 1 => ⟨((-29878029713/1099511627776), (53258031409/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((2940263239/549755813888), (-56206564991/2199023255552)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((10510722897/8796093022208), (2872169827/274877906944)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((-7454082307/4398046511104), (-15523848811/4398046511104)), (3/17592186044416), by norm_num⟩
  | 5 => ⟨((2187486737/2199023255552), (17228479611/17592186044416)), (3/35184372088832), by norm_num⟩
  | 6 => ⟨((-15582242171/35184372088832), (-7002521905/35184372088832)), (1/17592186044416), by norm_num⟩
  | 7 => ⟨((5848703161/35184372088832), (5573846171/562949953421312)), (7/281474976710656), by norm_num⟩
  | 8 => ⟨((-60774533399/1125899906842624), (19408143027/1125899906842624)), (7/562949953421312), by norm_num⟩
  | 9 => ⟨((67129921727/4503599627370496), (-54494390125/4503599627370496)), (25/4503599627370496), by norm_num⟩
  | 10 => ⟨((-3588026759/1125899906842624), (25464450411/4503599627370496)), (23/9007199254740992), by norm_num⟩
  | 11 => ⟨((10674141189/36028797018963968), (-78243937843/36028797018963968)), (43/36028797018963968), by norm_num⟩
  | 12 => ⟨((12845705131/72057594037927936), (51739157923/72057594037927936)), (75/144115188075855872), by norm_num⟩
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
  | 0 => ⟨((35/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((286720/1274281), (-36096/1274281)), 0, by norm_num⟩
  | 1 => ⟨((-40452718592/1623792066961), (10349445120/1623792066961)), 0, by norm_num⟩
  | 2 => ⟨((5612514951823360/2069167378879130041), (-2213787117551616/2069167378879130041)), 0, by norm_num⟩
  | 3 => ⟨((-81629079507/281474976710656), (44693435619/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((34201931009/1125899906842624), (-24737063669/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((-27979601387/9007199254740992), (13069587943/4503599627370496)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((44441008643/144115188075855872), (-1668504867/4503599627370496)), (1/36028797018963968), by norm_num⟩
  | 7 => ⟨((-33948188019/1152921504606846976), (13272379909/288230376151711744)), (5/1152921504606846976), by norm_num⟩
  | 8 => ⟨((12269358435/4611686018427387904), (-51628238559/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-16235565003/73786976294838206464), (24623451317/36893488147419103232)), (13/147573952589676412928), by norm_num⟩
  | 10 => ⟨((18064743963/1180591620717411303424), (-92325701333/1180591620717411303424)), (7/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-362348429/590295810358705651712), (42570971527/4722366482869645213696)), (15/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-4429173507/75557863725914323419136), (-77286460913/75557863725914323419136)), (1/4722366482869645213696), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (141/256)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (141/256)))⁻¹=value ((286720/1274281), (-36096/1274281)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((286720/1274281), (-36096/1274281))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3154092985/274877906944), (-63058950269/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-25640774289/4398046511104), (14781946199/1099511627776)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((2077766603/2199023255552), (-16487521389/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((4967499381/8796093022208), (111678602719/35184372088832)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((-41505452679/70368744177664), (-38537115267/35184372088832)), (5/70368744177664), by norm_num⟩
  | 5 => ⟨((23463468827/70368744177664), (43212706295/140737488355328)), (5/140737488355328), by norm_num⟩
  | 6 => ⟨((-10354608885/70368744177664), (-34935032611/562949953421312)), (11/562949953421312), by norm_num⟩
  | 7 => ⟨((124111518835/2251799813685248), (5441634839/2251799813685248)), (5/562949953421312), by norm_num⟩
  | 8 => ⟨((-80579203075/4503599627370496), (26645131763/4503599627370496)), (5/1125899906842624), by norm_num⟩
  | 9 => ⟨((2781117829/562949953421312), (-285968773/70368744177664)), (19/9007199254740992), by norm_num⟩
  | 10 => ⟨((-38014630811/36028797018963968), (68082595441/36028797018963968)), (33/36028797018963968), by norm_num⟩
  | 11 => ⟨((3497830833/36028797018963968), (-52211097235/72057594037927936)), (15/36028797018963968), by norm_num⟩
  | 12 => ⟨((8616788677/144115188075855872), (69002718831/288230376151711744)), (53/288230376151711744), by norm_num⟩
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
  | 0 => ⟨((43/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((352256/1913257), (-36096/1913257)), 0, by norm_num⟩
  | 1 => ⟨((-61390684160/3660552348049), (12715032576/3660552348049)), 0, by norm_num⟩
  | 2 => ⟨((10583137511800832/7003577403771185593), (-3347452325265408/7003577403771185593)), 0, by norm_num⟩
  | 3 => ⟨((-2367881997/17592186044416), (32794158719/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((53327875033/4503599627370496), (-933422259/140737488355328)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-74038747673/72057594037927936), (52043767869/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((25299289385/288230376151711744), (-43915129291/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 7 => ⟨((-33949422281/4611686018427387904), (36159855331/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 8 => ⟨((22273351791/36893488147419103232), (-58384061717/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-28400601749/590295810358705651712), (46358840149/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 10 => ⟨((34834478277/9444732965739290427392), (-9071090667/1180591620717411303424)), (3/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-10088778737/37778931862957161709568), (14018061473/18889465931478580854784)), (11/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((10628330429/604462909807314587353088), (-85634555791/1208925819614629174706176)), (19/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (141/256)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (141/256)))⁻¹=value ((352256/1913257), (-36096/1913257)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((352256/1913257), (-36096/1913257))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16203358971/8796093022208), (-50248337431/17592186044416)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-33860802491/35184372088832), (25205605159/8796093022208)), (5/35184372088832), by norm_num⟩
  | 2 => ⟨((6619651475/70368744177664), (-29398562093/17592186044416)), (5/70368744177664), by norm_num⟩
  | 3 => ⟨((3007618475/17592186044416), (102522109831/140737488355328)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-21373687895/140737488355328), (-36025542223/140737488355328)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((735159831/8796093022208), (40741865225/562949953421312)), (3/281474976710656), by norm_num⟩
  | 6 => ⟨((-82504277775/2251799813685248), (-8175909379/562949953421312)), (3/562949953421312), by norm_num⟩
  | 7 => ⟨((123427217809/9007199254740992), (3570682247/9007199254740992)), (11/4503599627370496), by norm_num⟩
  | 8 => ⟨((-80123980057/18014398509481984), (6843750265/4503599627370496)), (21/18014398509481984), by norm_num⟩
  | 9 => ⟨((44243706207/36028797018963968), (-18433452711/18014398509481984)), (21/36028797018963968), by norm_num⟩
  | 10 => ⟨((-2359922635/9007199254740992), (68253211317/144115188075855872)), (9/36028797018963968), by norm_num⟩
  | 11 => ⟨((859508859/36028797018963968), (-52257639287/288230376151711744)), (1/9007199254740992), by norm_num⟩
  | 12 => ⟨((17338873819/1152921504606846976), (34509416493/576460752303423488)), (57/1152921504606846976), by norm_num⟩
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
  | 0 => ⟨((51/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((139264/894435), (-12032/894435)), 0, by norm_num⟩
  | 1 => ⟨((-3208282112/266671323075), (1675624448/800013969225)), 0, by norm_num⟩
  | 2 => ⟨((660116743389184/715560494563762875), (-174580157120512/715560494563762875)), 0, by norm_num⟩
  | 3 => ⟨((-9876562499/140737488355328), (14185516055/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((23841277545/4503599627370496), (-21921064429/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((-14258630543/36028797018963968), (32436401701/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((33775873755/1152921504606846976), (-46540776399/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-39567091823/18446744073709551616), (32620536139/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 8 => ⟨((45774426849/295147905179352825856), (-11222587653/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-52185874499/4722366482869645213696), (1901302971/147573952589676412928)), (3/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((14613843043/18889465931478580854784), (-5087545917/4722366482869645213696)), (9/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-16013048037/302231454903657293676544), (53841931281/604462909807314587353088)), (13/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((34097557689/9671406556917033397649408), (-35256136917/4835703278458516698824704)), (19/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (141/256)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (141/256)))⁻¹=value ((139264/894435), (-12032/894435)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((139264/894435), (-12032/894435))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17479196013/70368744177664), (-66077039421/140737488355328)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-17940582621/140737488355328), (69993653141/140737488355328)), (5/140737488355328), by norm_num⟩
  | 2 => ⟨((-176505699/140737488355328), (-42366761927/140737488355328)), (5/281474976710656), by norm_num⟩
  | 3 => ⟨((10848275715/281474976710656), (75744613249/562949953421312)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-8724296479/281474976710656), (-27037508655/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((4707020251/281474976710656), (30792497291/2251799813685248)), (11/4503599627370496), by norm_num⟩
  | 6 => ⟨((-32849088963/4503599627370496), (-12252095693/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 7 => ⟨((49090304495/18014398509481984), (1445501681/36028797018963968)), (19/36028797018963968), by norm_num⟩
  | 8 => ⟨((-63734599373/72057594037927936), (22456207823/72057594037927936)), (9/36028797018963968), by norm_num⟩
  | 9 => ⟨((35192757143/144115188075855872), (-59390538127/288230376151711744)), (35/288230376151711744), by norm_num⟩
  | 10 => ⟨((-30003785369/576460752303423488), (54733946009/576460752303423488)), (31/576460752303423488), by norm_num⟩
  | 11 => ⟨((2702929335/576460752303423488), (-20920937157/576460752303423488)), (27/1152921504606846976), by norm_num⟩
  | 12 => ⟨((6977400229/2305843009213693952), (13806785809/1152921504606846976)), (49/4611686018427387904), by norm_num⟩
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
  | 0 => ⟨((59/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((483328/3584425), (-36096/3584425)), 0, by norm_num⟩
  | 1 => ⟨((-116151517184/12848102580625), (17446207488/12848102580625)), 0, by norm_num⟩
  | 2 => ⟨((42409090363/70368744177664), (-9645336685/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-44970878741/1125899906842624), (3455315603/281474976710656)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((94795868647/36028797018963968), (-2316542251/2251799813685248)), (5/36028797018963968), by norm_num⟩
  | 5 => ⟨((-775570891/4503599627370496), (23809841081/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((51626217635/4611686018427387904), (-29683183909/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-6662422093/9223372036854775808), (2261201429/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 8 => ⟨((54580929291/1180591620717411303424), (-21660741381/590295810358705651712)), (11/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-55387983625/18889465931478580854784), (51129291519/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((55629565005/302231454903657293676544), (-29808410407/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-55206394623/4835703278458516698824704), (17198007239/1208925819614629174706176)), (19/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((27005368195/38685626227668133590597632), (-78655502719/77371252455336267181195264)), (23/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (141/256)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (141/256)))⁻¹=value ((483328/3584425), (-36096/3584425)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((483328/3584425), (-36096/3584425))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16193674451/562949953421312), (-37047773551/562949953421312)), (3/562949953421312), by norm_num⟩
  | 1 => ⟨((-15524704787/1125899906842624), (10263520593/140737488355328)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((-5940574669/2251799813685248), (-25650996557/562949953421312)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((31341112317/4503599627370496), (46867714929/2251799813685248)), (9/4503599627370496), by norm_num⟩
  | 4 => ⟨((-47171008573/9007199254740992), (-33922349917/4503599627370496)), (9/9007199254740992), by norm_num⟩
  | 5 => ⟨((12536327245/4503599627370496), (38856350129/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((-87150535801/72057594037927936), (-1913096189/4503599627370496)), (15/72057594037927936), by norm_num⟩
  | 7 => ⟨((130146192447/288230376151711744), (149289347/288230376151711744)), (27/288230376151711744), by norm_num⟩
  | 8 => ⟨((-84493826763/576460752303423488), (30649218815/576460752303423488)), (13/288230376151711744), by norm_num⟩
  | 9 => ⟨((46655749259/1152921504606846976), (-39851997725/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-19868041459/2305843009213693952), (73147315653/4611686018427387904)), (43/4611686018427387904), by norm_num⟩
  | 11 => ⟨((14164092981/18446744073709551616), (-55834978791/9223372036854775808)), (19/4611686018427387904), by norm_num⟩
  | 12 => ⟨((18717293323/36893488147419103232), (73651250069/36893488147419103232)), (69/36893488147419103232), by norm_num⟩
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
  | 0 => ⟨((67/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((548864/4616617), (-36096/4616617)), 0, by norm_num⟩
  | 1 => ⟨((-149974384640/21313152524689), (19811794944/21313152524689)), 0, by norm_num⟩
  | 2 => ⟨((58358030123/140737488355328), (-11648272649/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-27388163927/1125899906842624), (3682267329/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((51177031017/36028797018963968), (-34870424751/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((-47584434275/576460752303423488), (39567835987/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((44020567667/9223372036854775808), (-43586160533/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-40505264919/147573952589676412928), (23481096427/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 8 => ⟨((37056239351/2361183241434822606848), (-24866704865/2361183241434822606848)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-67378332407/75557863725914323419136), (6492208955/9444732965739290427392)), (5/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((60835540557/1208925819614629174706176), (-26806474519/604462909807314587353088)), (11/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-27253917857/9671406556917033397649408), (27398536489/9671406556917033397649408)), (3/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1512981995/9671406556917033397649408), (-55527509431/309485009821345068724781056)), (13/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (141/256)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (141/256)))⁻¹=value ((548864/4616617), (-36096/4616617)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((548864/4616617), (-36096/4616617))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((26169287163/9007199254740992), (-72498857255/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 1 => ⟨((-10902059337/9007199254740992), (20869235715/2251799813685248)), (9/9007199254740992), by norm_num⟩
  | 2 => ⟨((-11424539729/18014398509481984), (-107225840049/18014398509481984)), (5/9007199254740992), by norm_num⟩
  | 3 => ⟨((9467148849/9007199254740992), (3120343159/1125899906842624)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((-27195677661/36028797018963968), (-36576169617/36028797018963968)), (11/72057594037927936), by norm_num⟩
  | 5 => ⟨((57162652467/144115188075855872), (10522955913/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-49527297361/288230376151711744), (-32776423403/576460752303423488)), (19/576460752303423488), by norm_num⟩
  | 7 => ⟨((36964555749/576460752303423488), (-219259333/288230376151711744)), (17/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-12001352529/576460752303423488), (4475056489/576460752303423488)), (31/4611686018427387904), by norm_num⟩
  | 9 => ⟨((6627091259/1152921504606846976), (-22914451019/4611686018427387904)), (15/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-11276899743/9223372036854775808), (41891388003/18446744073709551616)), (13/9223372036854775808), by norm_num⟩
  | 11 => ⟨((1987765169/18446744073709551616), (-63861719579/73786976294838206464)), (23/36893488147419103232), by norm_num⟩
  | 12 => ⟨((21517122899/295147905179352825856), (84188920819/295147905179352825856)), (41/147573952589676412928), by norm_num⟩
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
  | 0 => ⟨((75/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((204800/1926627), (-12032/1926627)), 0, by norm_num⟩
  | 1 => ⟨((-6966378496/1237297199043), (2464153600/3711891597129)), 0, by norm_num⟩
  | 2 => ⟨((2125247125913600/7151430572101853883), (-378058527735808/7151430572101853883)), 0, by norm_num⟩
  | 3 => ⟨((-35195400557/2251799813685248), (8416573239/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((29509603363/36028797018963968), (-8915831695/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-24649468659/576460752303423488), (18112665327/1152921504606846976)), (5/2305843009213693952), by norm_num⟩
  | 6 => ⟨((82037598547/36893488147419103232), (-35731991073/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-16994854599/147573952589676412928), (4310636235/73786976294838206464)), (3/295147905179352825856), by norm_num⟩
  | 8 => ⟨((14021666141/2361183241434822606848), (-32722368241/9444732965739290427392)), (3/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-23030578037/75557863725914323419136), (30629180485/151115727451828646838272)), (3/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((75280119831/4835703278458516698824704), (-56696508401/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-61185465177/77371252455336267181195264), (51975666581/77371252455336267181195264)), (3/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((24717627331/618970019642690137449562112), (-47256890027/1237940039285380274899124224)), (3/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (141/256)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (141/256)))⁻¹=value ((204800/1926627), (-12032/1926627)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((204800/1926627), (-12032/1926627))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((18632205447/72057594037927936), (-31480166797/36028797018963968)), (7/72057594037927936), by norm_num⟩
  | 1 => ⟨((-5894210907/72057594037927936), (9367228407/9007199254740992)), (5/36028797018963968), by norm_num⟩
  | 2 => ⟨((-7456973741/72057594037927936), (-98616557335/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 3 => ⟨((39393247159/288230376151711744), (93410916707/288230376151711744)), (13/288230376151711744), by norm_num⟩
  | 4 => ⟨((-27339958719/288230376151711744), (-34587357723/288230376151711744)), (13/576460752303423488), by norm_num⟩
  | 5 => ⟨((56958424047/1152921504606846976), (9987671271/288230376151711744)), (13/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-98481708799/4611686018427387904), (-30706227063/4611686018427387904)), (21/4611686018427387904), by norm_num⟩
  | 7 => ⟨((18371426781/2305843009213693952), (-1790359597/9223372036854775808)), (9/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-95459464647/36893488147419103232), (18269952947/18446744073709551616)), (33/36893488147419103232), by norm_num⟩
  | 9 => ⟨((13178699609/18446744073709551616), (-46101914109/73786976294838206464)), (1/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-44804874139/295147905179352825856), (83961996891/295147905179352825856)), (55/295147905179352825856), by norm_num⟩
  | 11 => ⟨((7809374419/590295810358705651712), (-63910081123/590295810358705651712)), (3/36893488147419103232), by norm_num⟩
  | 12 => ⟨((21642256311/2361183241434822606848), (84203880513/2361183241434822606848)), (43/1180591620717411303424), by norm_num⟩
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
  | 0 => ⟨((83/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((679936/7074217), (-36096/7074217)), 0, by norm_num⟩
  | 1 => ⟨((-230505021440/50044546163089), (24542969856/50044546163089)), 0, by norm_num⟩
  | 2 => ⟨((61952850349/281474976710656), (-9941522389/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-23615404539/2251799813685248), (20346221335/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((35901323127/72057594037927936), (-19500464765/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((-27207146915/1152921504606846976), (4481303395/576460752303423488)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((41108389839/36893488147419103232), (-32008373779/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-15477832825/295147905179352825856), (27967864161/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 8 => ⟨((23231526505/9444732965739290427392), (-24032182333/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-17372628947/151115727451828646838272), (20375373035/302231454903657293676544)), (5/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((25884512399/4835703278458516698824704), (-34170542337/9671406556917033397649408)), (9/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-76822531735/309485009821345068724781056), (56775044573/309485009821345068724781056)), (1/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((56752630493/4951760157141521099596496896), (-46791194347/4951760157141521099596496896)), (7/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (141/256)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (141/256)))⁻¹=value ((679936/7074217), (-36096/7074217)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((679936/7074217), (-36096/7074217))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((23513196819/1152921504606846976), (-12292963439/144115188075855872)), (3/288230376151711744), by norm_num⟩
  | 1 => ⟨((-956378397/288230376151711744), (3765915997/36028797018963968)), (9/576460752303423488), by norm_num⟩
  | 2 => ⟨((-7808351387/576460752303423488), (-40510155545/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 3 => ⟨((36017561571/2305843009213693952), (38962402273/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 4 => ⟨((-48727457677/4611686018427387904), (-58263552585/4611686018427387904)), (13/4611686018427387904), by norm_num⟩
  | 5 => ⟨((50407808721/9223372036854775808), (33745094685/9223372036854775808)), (13/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-5438246227/2305843009213693952), (-399420875/576460752303423488)), (5/9223372036854775808), by norm_num⟩
  | 7 => ⟨((64924908783/73786976294838206464), (-2363312115/73786976294838206464)), (17/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-84365239321/295147905179352825856), (33109654299/295147905179352825856)), (31/295147905179352825856), by norm_num⟩
  | 9 => ⟨((23295623619/295147905179352825856), (-41213161693/590295810358705651712)), (15/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-39559559637/2361183241434822606848), (4674162423/147573952589676412928)), (51/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((1704156227/1180591620717411303424), (-28425142985/2361183241434822606848)), (89/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((19348088723/18889465931478580854784), (74860245933/18889465931478580854784)), (79/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((91/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((745472/8499625), (-36096/8499625)), 0, by norm_num⟩
  | 1 => ⟨((-277212790784/72243625140625), (26908557312/72243625140625)), 0, by norm_num⟩
  | 2 => ⟨((94284232035/562949953421312), (-13782054633/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-65686453677/9007199254740992), (6436716665/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((91303289349/288230376151711744), (-5632155453/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-31648856313/2305843009213693952), (18909201563/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((87541040245/147573952589676412928), (-30836324271/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-15093919177/590295810358705651712), (6152623843/590295810358705651712)), (3/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((83053143687/75557863725914323419136), (-38638421121/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-28480833299/604462909807314587353088), (14966188435/604462909807314587353088)), (1/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((77900638575/38685626227668133590597632), (-22937329275/19342813113834066795298816)), (13/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-53100557415/618970019642690137449562112), (34834642619/618970019642690137449562112)), (5/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((36074615035/9903520314283042199192993792), (-26245834067/9903520314283042199192993792)), (1/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (141/256)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (141/256)))⁻¹=value ((745472/8499625), (-36096/8499625)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((745472/8499625), (-36096/8499625))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((205576943/144115188075855872), (-34900933949/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 1 => ⟨((981272893/9223372036854775808), (87774502195/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-13939497371/9223372036854775808), (-15041145627/2305843009213693952)), (9/9223372036854775808), by norm_num⟩
  | 3 => ⟨((14698652293/9223372036854775808), (58670025029/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-38996651365/36893488147419103232), (-22123069069/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 5 => ⟨((5015418381/9223372036854775808), (51359597077/147573952589676412928)), (11/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-8647102295/36893488147419103232), (-9571946839/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 7 => ⟨((103245863909/1180591620717411303424), (-2478729339/590295810358705651712)), (29/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-67104411909/2361183241434822606848), (13485474503/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((9265398079/1180591620717411303424), (-33150687709/4722366482869645213696)), (13/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-31435730403/18889465931478580854784), (29973994569/9444732965739290427392)), (43/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((10707967669/75557863725914323419136), (-22756006629/18889465931478580854784)), (75/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1945792077/18889465931478580854784), (59897349243/151115727451828646838272)), (33/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((99/8), (141/256)), 0, by norm_num⟩
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
  | 0 => ⟨((90112/1117345), (-12032/3352035)), 0, by norm_num⟩
  | 1 => ⟨((-36468391936/11236138641225), (1084227584/3745379547075)), 0, by norm_num⟩
  | 2 => ⟨((9173122917/70368744177664), (-9850633121/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-94128277479/18014398509481984), (16925593557/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((60244271385/288230376151711744), (-1702890541/36028797018963968)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-76955196075/9223372036854775808), (5259706431/2305843009213693952)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((98092630823/295147905179352825856), (-31567579265/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-7797695529/590295810358705651712), (23183776165/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((39582009981/75557863725914323419136), (-8374595485/37778931862957161709568)), (3/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-50113634181/2417851639229258349412352), (2985744501/302231454903657293676544)), (5/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((63293485121/77371252455336267181195264), (-8424972949/19342813113834066795298816)), (1/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-79736783157/2475880078570760549798248448), (47120468189/2475880078570760549798248448)), (3/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((25046002847/19807040628566084398385987584), (-32691190547/39614081257132168796771975168)), (9/39614081257132168796771975168), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (141/256)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (141/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (141/256)))⁻¹=value ((90112/1117345), (-12032/3352035)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((90112/1117345), (-12032/3352035))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((405266387/4611686018427387904), (-11353259661/18446744073709551616)), (7/73786976294838206464), by norm_num⟩
  | 1 => ⟨((1486820645/36893488147419103232), (116891266427/147573952589676412928)), (21/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-1368255993/9223372036854775808), (-81537066457/147573952589676412928)), (7/73786976294838206464), by norm_num⟩
  | 3 => ⟨((43361228387/295147905179352825856), (80515144675/295147905179352825856)), (17/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-56647365465/590295810358705651712), (-61192165505/590295810358705651712)), (19/590295810358705651712), by norm_num⟩
  | 5 => ⟨((58037078391/1180591620717411303424), (35563895559/1180591620717411303424)), (9/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-99979866553/4722366482869645213696), (-6512384931/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((74627201401/9444732965739290427392), (-4421284281/9444732965739290427392)), (23/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-48523065225/18889465931478580854784), (19952684513/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((26801381557/37778931862957161709568), (-48471900545/75557863725914323419136)), (39/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-45418896839/302231454903657293676544), (87363838713/302231454903657293676544)), (65/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((3822093993/302231454903657293676544), (-4140233971/37778931862957161709568)), (57/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((5692236831/604462909807314587353088), (43567853159/1208925819614629174706176)), (25/604462909807314587353088), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((104862918319/137438953472), (-557442019/34359738368)), (635/137438953472), by norm_num⟩
  | 1 => ⟨((6663247185/274877906944), (27796085115/137438953472)), (1597/137438953472), by norm_num⟩
  | 2 => ⟨((55124887359/1099511627776), (-21347212895/549755813888)), (8789/549755813888), by norm_num⟩
  | 3 => ⟨((6499973595/1099511627776), (7695920533/274877906944)), (34263/2199023255552), by norm_num⟩
  | 4 => ⟨((-20471304075/8796093022208), (-7544248619/1099511627776)), (104561/8796093022208), by norm_num⟩
  | 5 => ⟨((36488526195/17592186044416), (38996556115/17592186044416)), (32941/4398046511104), by norm_num⟩
  | 6 => ⟨((-61509188113/70368744177664), (-28936592991/70368744177664)), (70885/17592186044416), by norm_num⟩
  | 7 => ⟨((94436400683/281474976710656), (7756562659/281474976710656)), (533993/281474976710656), by norm_num⟩
  | 8 => ⟨((-61030438027/562949953421312), (4725251063/140737488355328)), (226813/281474976710656), by norm_num⟩
  | 9 => ⟨((67544670669/2251799813685248), (-27003979171/1125899906842624)), (360469/1125899906842624), by norm_num⟩
  | 10 => ⟨((-1805889569/281474976710656), (50796256261/4503599627370496)), (552087/4503599627370496), by norm_num⟩
  | 11 => ⟨((2714583641/4503599627370496), (-78163613493/18014398509481984)), (823867/18014398509481984), by norm_num⟩
  | 12 => ⟨((25531437609/72057594037927936), (103451018047/72057594037927936)), (1197109/72057594037927936), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((104862918319/137438953472), (-557442019/34359738368)), (159/34359738368), by norm_num⟩
  | 1 => ⟨((6663247185/274877906944), (27796085115/137438953472)), (6389/549755813888), by norm_num⟩
  | 2 => ⟨((55124887359/1099511627776), (-21347212895/549755813888)), (17579/1099511627776), by norm_num⟩
  | 3 => ⟨((6499973595/1099511627776), (7695920533/274877906944)), (4283/274877906944), by norm_num⟩
  | 4 => ⟨((-20471304075/8796093022208), (-7544248619/1099511627776)), (52281/4398046511104), by norm_num⟩
  | 5 => ⟨((36488526195/17592186044416), (38996556115/17592186044416)), (131765/17592186044416), by norm_num⟩
  | 6 => ⟨((-61509188113/70368744177664), (-28936592991/70368744177664)), (283543/70368744177664), by norm_num⟩
  | 7 => ⟨((94436400683/281474976710656), (7756562659/281474976710656)), (534005/281474976710656), by norm_num⟩
  | 8 => ⟨((-61030438027/562949953421312), (4725251063/140737488355328)), (453649/562949953421312), by norm_num⟩
  | 9 => ⟨((67544670669/2251799813685248), (-27003979171/1125899906842624)), (721029/2251799813685248), by norm_num⟩
  | 10 => ⟨((-1805889569/281474976710656), (50796256261/4503599627370496)), (138067/1125899906842624), by norm_num⟩
  | 11 => ⟨((2714583641/4503599627370496), (-78163613493/18014398509481984)), (206147/4503599627370496), by norm_num⟩
  | 12 => ⟨((25531437609/72057594037927936), (103451018047/72057594037927936)), (149999/9007199254740992), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile002Gamma
