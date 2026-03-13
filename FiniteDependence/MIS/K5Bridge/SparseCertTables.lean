import FiniteDependence.MIS.K5Bridge.Step3SparseCore

namespace FiniteDependence.MIS

namespace K5Bridge

namespace Model

open Step3

noncomputable section

@[simp] theorem words14_eq_explicit : words14 =
    ["00100100100100", "00100100100101", "00100100101001", "00100100101010", "00100101001001", "00100101001010", "00100101010010", "00100101010100", "00100101010101", "00101001001001", "00101001001010", "00101001010010", "00101001010100", "00101001010101", "00101010010010", "00101010010100", "00101010010101", "00101010100100", "00101010100101", "00101010101001", "00101010101010", "01001001001001", "01001001001010", "01001001010010", "01001001010100", "01001001010101", "01001010010010", "01001010010100", "01001010010101", "01001010100100", "01001010100101", "01001010101001", "01001010101010", "01010010010010", "01010010010100", "01010010010101", "01010010100100", "01010010100101", "01010010101001", "01010010101010", "01010100100100", "01010100100101", "01010100101001", "01010100101010", "01010101001001", "01010101001010", "01010101010010", "01010101010100", "01010101010101", "10010010010010", "10010010010100", "10010010010101", "10010010100100", "10010010100101", "10010010101001", "10010010101010", "10010100100100", "10010100100101", "10010100101001", "10010100101010", "10010101001001", "10010101001010", "10010101010010", "10010101010100", "10010101010101", "10100100100100", "10100100100101", "10100100101001", "10100100101010", "10100101001001", "10100101001010", "10100101010010", "10100101010100", "10100101010101", "10101001001001", "10101001001010", "10101001010010", "10101001010100", "10101001010101", "10101010010010", "10101010010100", "10101010010101", "10101010100100", "10101010100101", "10101010101001", "10101010101010"] := by
  decide

@[simp] theorem words7_eq_explicit : words7 =
    ["0010010", "0010100", "0010101", "0100100", "0100101", "0101001", "0101010", "1001001", "1001010", "1010010", "1010100", "1010101"] := by
  decide

@[simp] theorem len_1 : ("1" : String).length = 1 := by
  decide

@[simp] theorem len_00 : ("00" : String).length = 2 := by
  decide

@[simp] theorem len_01 : ("01" : String).length = 2 := by
  decide

@[simp] theorem len_10 : ("10" : String).length = 2 := by
  decide

@[simp] theorem len_001 : ("001" : String).length = 3 := by
  decide

@[simp] theorem len_010 : ("010" : String).length = 3 := by
  decide

@[simp] theorem len_100 : ("100" : String).length = 3 := by
  decide

@[simp] theorem len_101 : ("101" : String).length = 3 := by
  decide

@[simp] theorem len_0010 : ("0010" : String).length = 4 := by
  decide

@[simp] theorem len_0100 : ("0100" : String).length = 4 := by
  decide

@[simp] theorem len_0101 : ("0101" : String).length = 4 := by
  decide

@[simp] theorem len_1001 : ("1001" : String).length = 4 := by
  decide

@[simp] theorem len_1010 : ("1010" : String).length = 4 := by
  decide

@[simp] theorem len_00100 : ("00100" : String).length = 5 := by
  decide

@[simp] theorem len_00101 : ("00101" : String).length = 5 := by
  decide

@[simp] theorem len_01010 : ("01010" : String).length = 5 := by
  decide

@[simp] theorem len_10010 : ("10010" : String).length = 5 := by
  decide

@[simp] theorem len_10100 : ("10100" : String).length = 5 := by
  decide

@[simp] theorem len_10101 : ("10101" : String).length = 5 := by
  decide

@[simp] theorem len_001001 : ("001001" : String).length = 6 := by
  decide

@[simp] theorem len_001010 : ("001010" : String).length = 6 := by
  decide

@[simp] theorem len_010010 : ("010010" : String).length = 6 := by
  decide

@[simp] theorem len_010100 : ("010100" : String).length = 6 := by
  decide

@[simp] theorem len_010101 : ("010101" : String).length = 6 := by
  decide

@[simp] theorem len_100100 : ("100100" : String).length = 6 := by
  decide

@[simp] theorem len_100101 : ("100101" : String).length = 6 := by
  decide

@[simp] theorem len_101001 : ("101001" : String).length = 6 := by
  decide

@[simp] theorem len_101010 : ("101010" : String).length = 6 := by
  decide

@[simp] theorem len_0010010 : ("0010010" : String).length = 7 := by
  decide

@[simp] theorem len_0010100 : ("0010100" : String).length = 7 := by
  decide

@[simp] theorem len_0010101 : ("0010101" : String).length = 7 := by
  decide

@[simp] theorem len_0100100 : ("0100100" : String).length = 7 := by
  decide

@[simp] theorem len_0100101 : ("0100101" : String).length = 7 := by
  decide

@[simp] theorem len_0101001 : ("0101001" : String).length = 7 := by
  decide

@[simp] theorem len_0101010 : ("0101010" : String).length = 7 := by
  decide

@[simp] theorem len_1001001 : ("1001001" : String).length = 7 := by
  decide

@[simp] theorem len_1001010 : ("1001010" : String).length = 7 := by
  decide

@[simp] theorem len_1010010 : ("1010010" : String).length = 7 := by
  decide

@[simp] theorem len_1010100 : ("1010100" : String).length = 7 := by
  decide

@[simp] theorem len_1010101 : ("1010101" : String).length = 7 := by
  decide

@[simp] theorem len_00100100 : ("00100100" : String).length = 8 := by
  decide

@[simp] theorem len_01001001 : ("01001001" : String).length = 8 := by
  decide

@[simp] theorem len_10100101 : ("10100101" : String).length = 8 := by
  decide

@[simp] theorem len_100100100 : ("100100100" : String).length = 9 := by
  decide

@[simp] theorem len_100100101 : ("100100101" : String).length = 9 := by
  decide

@[simp] theorem len_101001001 : ("101001001" : String).length = 9 := by
  decide

@[simp] theorem len_0010010100 : ("0010010100" : String).length = 10 := by
  decide

@[simp] theorem len_0010100101 : ("0010100101" : String).length = 10 := by
  decide

@[simp] theorem len_1010010100 : ("1010010100" : String).length = 10 := by
  decide

@[simp] theorem len_1010010101 : ("1010010101" : String).length = 10 := by
  decide

@[simp] theorem len_1010100101 : ("1010100101" : String).length = 10 := by
  decide

@[simp] theorem len_00101001001 : ("00101001001" : String).length = 11 := by
  decide

@[simp] theorem len_01001001001 : ("01001001001" : String).length = 11 := by
  decide

@[simp] theorem len_10010010101 : ("10010010101" : String).length = 11 := by
  decide

@[simp] theorem len_001010010100 : ("001010010100" : String).length = 12 := by
  decide

@[simp] theorem len_100100100100 : ("100100100100" : String).length = 12 := by
  decide

@[simp] theorem len_0010010010010 : ("0010010010010" : String).length = 13 := by
  decide

@[simp] theorem len_0010010010100 : ("0010010010100" : String).length = 13 := by
  decide

@[simp] theorem len_0010010010101 : ("0010010010101" : String).length = 13 := by
  decide

@[simp] theorem len_0010010100100 : ("0010010100100" : String).length = 13 := by
  decide

@[simp] theorem len_0010010100101 : ("0010010100101" : String).length = 13 := by
  decide

@[simp] theorem len_0010010101010 : ("0010010101010" : String).length = 13 := by
  decide

@[simp] theorem len_0010100100100 : ("0010100100100" : String).length = 13 := by
  decide

@[simp] theorem len_0010100100101 : ("0010100100101" : String).length = 13 := by
  decide

@[simp] theorem len_0010100101001 : ("0010100101001" : String).length = 13 := by
  decide

@[simp] theorem len_0010100101010 : ("0010100101010" : String).length = 13 := by
  decide

@[simp] theorem len_0010101001001 : ("0010101001001" : String).length = 13 := by
  decide

@[simp] theorem len_0010101010101 : ("0010101010101" : String).length = 13 := by
  decide

@[simp] theorem len_0100100100100 : ("0100100100100" : String).length = 13 := by
  decide

@[simp] theorem len_0100100100101 : ("0100100100101" : String).length = 13 := by
  decide

@[simp] theorem len_0100100101001 : ("0100100101001" : String).length = 13 := by
  decide

@[simp] theorem len_0100101001001 : ("0100101001001" : String).length = 13 := by
  decide

@[simp] theorem len_0100101010100 : ("0100101010100" : String).length = 13 := by
  decide

@[simp] theorem len_0100101010101 : ("0100101010101" : String).length = 13 := by
  decide

@[simp] theorem len_0101001001001 : ("0101001001001" : String).length = 13 := by
  decide

@[simp] theorem len_0101001001010 : ("0101001001010" : String).length = 13 := by
  decide

@[simp] theorem len_0101001010010 : ("0101001010010" : String).length = 13 := by
  decide

@[simp] theorem len_0101001010100 : ("0101001010100" : String).length = 13 := by
  decide

@[simp] theorem len_0101001010101 : ("0101001010101" : String).length = 13 := by
  decide

@[simp] theorem len_0101010010100 : ("0101010010100" : String).length = 13 := by
  decide

@[simp] theorem len_0101010010101 : ("0101010010101" : String).length = 13 := by
  decide

@[simp] theorem len_0101010101010 : ("0101010101010" : String).length = 13 := by
  decide

@[simp] theorem len_1001001001001 : ("1001001001001" : String).length = 13 := by
  decide

@[simp] theorem len_1001001001010 : ("1001001001010" : String).length = 13 := by
  decide

@[simp] theorem len_1001001010010 : ("1001001010010" : String).length = 13 := by
  decide

@[simp] theorem len_1001001010100 : ("1001001010100" : String).length = 13 := by
  decide

@[simp] theorem len_1001010010010 : ("1001010010010" : String).length = 13 := by
  decide

@[simp] theorem len_1001010010101 : ("1001010010101" : String).length = 13 := by
  decide

@[simp] theorem len_1001010101001 : ("1001010101001" : String).length = 13 := by
  decide

@[simp] theorem len_1010010010010 : ("1010010010010" : String).length = 13 := by
  decide

@[simp] theorem len_1010010010100 : ("1010010010100" : String).length = 13 := by
  decide

@[simp] theorem len_1010010010101 : ("1010010010101" : String).length = 13 := by
  decide

@[simp] theorem len_1010010100100 : ("1010010100100" : String).length = 13 := by
  decide

@[simp] theorem len_1010010100101 : ("1010010100101" : String).length = 13 := by
  decide

@[simp] theorem len_1010010101001 : ("1010010101001" : String).length = 13 := by
  decide

@[simp] theorem len_1010010101010 : ("1010010101010" : String).length = 13 := by
  decide

@[simp] theorem len_1010100100100 : ("1010100100100" : String).length = 13 := by
  decide

@[simp] theorem len_1010100100101 : ("1010100100101" : String).length = 13 := by
  decide

@[simp] theorem len_1010100101001 : ("1010100101001" : String).length = 13 := by
  decide

@[simp] theorem len_1010101010100 : ("1010101010100" : String).length = 13 := by
  decide

@[simp] theorem len_1010101010101 : ("1010101010101" : String).length = 13 := by
  decide

@[simp] theorem len_01010101001001 : ("01010101001001" : String).length = 14 := by
  decide

@[simp] theorem len_10010010010101 : ("10010010010101" : String).length = 14 := by
  decide

@[simp] theorem len_10100101001001 : ("10100101001001" : String).length = 14 := by
  decide

@[simp] theorem row_1 : allRows[1]? = some (RowKind.stat13 "0010010010010") := by
  decide

@[simp] theorem row_2 : allRows[2]? = some (RowKind.stat13 "0010010010100") := by
  decide

@[simp] theorem row_3 : allRows[3]? = some (RowKind.stat13 "0010010010101") := by
  decide

@[simp] theorem row_4 : allRows[4]? = some (RowKind.stat13 "0010010100100") := by
  decide

@[simp] theorem row_5 : allRows[5]? = some (RowKind.stat13 "0010010100101") := by
  decide

@[simp] theorem row_7 : allRows[7]? = some (RowKind.stat13 "0010010101010") := by
  decide

@[simp] theorem row_8 : allRows[8]? = some (RowKind.stat13 "0010100100100") := by
  decide

@[simp] theorem row_9 : allRows[9]? = some (RowKind.stat13 "0010100100101") := by
  decide

@[simp] theorem row_10 : allRows[10]? = some (RowKind.stat13 "0010100101001") := by
  decide

@[simp] theorem row_11 : allRows[11]? = some (RowKind.stat13 "0010100101010") := by
  decide

@[simp] theorem row_12 : allRows[12]? = some (RowKind.stat13 "0010101001001") := by
  decide

@[simp] theorem row_16 : allRows[16]? = some (RowKind.stat13 "0010101010101") := by
  decide

@[simp] theorem row_17 : allRows[17]? = some (RowKind.stat13 "0100100100100") := by
  decide

@[simp] theorem row_18 : allRows[18]? = some (RowKind.stat13 "0100100100101") := by
  decide

@[simp] theorem row_19 : allRows[19]? = some (RowKind.stat13 "0100100101001") := by
  decide

@[simp] theorem row_21 : allRows[21]? = some (RowKind.stat13 "0100101001001") := by
  decide

@[simp] theorem row_24 : allRows[24]? = some (RowKind.stat13 "0100101010100") := by
  decide

@[simp] theorem row_25 : allRows[25]? = some (RowKind.stat13 "0100101010101") := by
  decide

@[simp] theorem row_26 : allRows[26]? = some (RowKind.stat13 "0101001001001") := by
  decide

@[simp] theorem row_27 : allRows[27]? = some (RowKind.stat13 "0101001001010") := by
  decide

@[simp] theorem row_28 : allRows[28]? = some (RowKind.stat13 "0101001010010") := by
  decide

@[simp] theorem row_29 : allRows[29]? = some (RowKind.stat13 "0101001010100") := by
  decide

@[simp] theorem row_30 : allRows[30]? = some (RowKind.stat13 "0101001010101") := by
  decide

@[simp] theorem row_32 : allRows[32]? = some (RowKind.stat13 "0101010010100") := by
  decide

@[simp] theorem row_37 : allRows[37]? = some (RowKind.stat13 "0101010101010") := by
  decide

@[simp] theorem row_38 : allRows[38]? = some (RowKind.stat13 "1001001001001") := by
  decide

@[simp] theorem row_39 : allRows[39]? = some (RowKind.stat13 "1001001001010") := by
  decide

@[simp] theorem row_40 : allRows[40]? = some (RowKind.stat13 "1001001010010") := by
  decide

@[simp] theorem row_41 : allRows[41]? = some (RowKind.stat13 "1001001010100") := by
  decide

@[simp] theorem row_43 : allRows[43]? = some (RowKind.stat13 "1001010010010") := by
  decide

@[simp] theorem row_45 : allRows[45]? = some (RowKind.stat13 "1001010010101") := by
  decide

@[simp] theorem row_48 : allRows[48]? = some (RowKind.stat13 "1001010101001") := by
  decide

@[simp] theorem row_50 : allRows[50]? = some (RowKind.stat13 "1010010010010") := by
  decide

@[simp] theorem row_51 : allRows[51]? = some (RowKind.stat13 "1010010010100") := by
  decide

@[simp] theorem row_52 : allRows[52]? = some (RowKind.stat13 "1010010010101") := by
  decide

@[simp] theorem row_53 : allRows[53]? = some (RowKind.stat13 "1010010100100") := by
  decide

@[simp] theorem row_54 : allRows[54]? = some (RowKind.stat13 "1010010100101") := by
  decide

@[simp] theorem row_55 : allRows[55]? = some (RowKind.stat13 "1010010101001") := by
  decide

@[simp] theorem row_56 : allRows[56]? = some (RowKind.stat13 "1010010101010") := by
  decide

@[simp] theorem row_57 : allRows[57]? = some (RowKind.stat13 "1010100100100") := by
  decide

@[simp] theorem row_58 : allRows[58]? = some (RowKind.stat13 "1010100100101") := by
  decide

@[simp] theorem row_59 : allRows[59]? = some (RowKind.stat13 "1010100101001") := by
  decide

@[simp] theorem row_64 : allRows[64]? = some (RowKind.stat13 "1010101010100") := by
  decide

@[simp] theorem row_65 : allRows[65]? = some (RowKind.stat13 "1010101010101") := by
  decide

@[simp] theorem row_66 : allRows[66]? = some (RowKind.split 2 "00" 7 "0010010") := by
  decide

@[simp] theorem row_67 : allRows[67]? = some (RowKind.split 2 "00" 7 "0010100") := by
  decide

@[simp] theorem row_68 : allRows[68]? = some (RowKind.split 2 "00" 7 "0010101") := by
  decide

@[simp] theorem row_69 : allRows[69]? = some (RowKind.split 2 "00" 7 "0100100") := by
  decide

@[simp] theorem row_70 : allRows[70]? = some (RowKind.split 2 "00" 7 "0100101") := by
  decide

@[simp] theorem row_71 : allRows[71]? = some (RowKind.split 2 "00" 7 "0101001") := by
  decide

@[simp] theorem row_72 : allRows[72]? = some (RowKind.split 2 "00" 7 "0101010") := by
  decide

@[simp] theorem row_73 : allRows[73]? = some (RowKind.split 2 "00" 7 "1001001") := by
  decide

@[simp] theorem row_74 : allRows[74]? = some (RowKind.split 2 "00" 7 "1001010") := by
  decide

@[simp] theorem row_75 : allRows[75]? = some (RowKind.split 2 "00" 7 "1010010") := by
  decide

@[simp] theorem row_76 : allRows[76]? = some (RowKind.split 2 "00" 7 "1010100") := by
  decide

@[simp] theorem row_78 : allRows[78]? = some (RowKind.split 2 "01" 7 "0010010") := by
  decide

@[simp] theorem row_79 : allRows[79]? = some (RowKind.split 2 "01" 7 "0010100") := by
  decide

@[simp] theorem row_80 : allRows[80]? = some (RowKind.split 2 "01" 7 "0010101") := by
  decide

@[simp] theorem row_85 : allRows[85]? = some (RowKind.split 2 "01" 7 "1001001") := by
  decide

@[simp] theorem row_86 : allRows[86]? = some (RowKind.split 2 "01" 7 "1001010") := by
  decide

@[simp] theorem row_87 : allRows[87]? = some (RowKind.split 2 "01" 7 "1010010") := by
  decide

@[simp] theorem row_88 : allRows[88]? = some (RowKind.split 2 "01" 7 "1010100") := by
  decide

@[simp] theorem row_91 : allRows[91]? = some (RowKind.split 2 "10" 7 "0010100") := by
  decide

@[simp] theorem row_96 : allRows[96]? = some (RowKind.split 2 "10" 7 "0101010") := by
  decide

@[simp] theorem row_97 : allRows[97]? = some (RowKind.split 2 "10" 7 "1001001") := by
  decide

@[simp] theorem row_98 : allRows[98]? = some (RowKind.split 2 "10" 7 "1001010") := by
  decide

@[simp] theorem row_99 : allRows[99]? = some (RowKind.split 2 "10" 7 "1010010") := by
  decide

@[simp] theorem row_101 : allRows[101]? = some (RowKind.split 2 "10" 7 "1010101") := by
  decide

@[simp] theorem row_104 : allRows[104]? = some (RowKind.split 3 "001" 6 "010010") := by
  decide

@[simp] theorem row_121 : allRows[121]? = some (RowKind.split 3 "100" 6 "001010") := by
  decide

@[simp] theorem row_122 : allRows[122]? = some (RowKind.split 3 "100" 6 "010010") := by
  decide

@[simp] theorem row_124 : allRows[124]? = some (RowKind.split 3 "100" 6 "010101") := by
  decide

@[simp] theorem row_126 : allRows[126]? = some (RowKind.split 3 "100" 6 "100101") := by
  decide

@[simp] theorem row_127 : allRows[127]? = some (RowKind.split 3 "100" 6 "101001") := by
  decide

@[simp] theorem row_128 : allRows[128]? = some (RowKind.split 3 "100" 6 "101010") := by
  decide

@[simp] theorem row_130 : allRows[130]? = some (RowKind.split 3 "101" 6 "001010") := by
  decide

@[simp] theorem row_131 : allRows[131]? = some (RowKind.split 3 "101" 6 "010010") := by
  decide

@[simp] theorem row_132 : allRows[132]? = some (RowKind.split 3 "101" 6 "010100") := by
  decide

@[simp] theorem row_137 : allRows[137]? = some (RowKind.split 3 "101" 6 "101010") := by
  decide

@[simp] theorem row_141 : allRows[141]? = some (RowKind.split 4 "0010" 5 "01010") := by
  decide

@[simp] theorem row_150 : allRows[150]? = some (RowKind.split 4 "0100" 5 "10100") := by
  decide

@[simp] theorem row_153 : allRows[153]? = some (RowKind.split 4 "0101" 5 "00101") := by
  decide

@[simp] theorem row_162 : allRows[162]? = some (RowKind.split 4 "1001" 5 "01010") := by
  decide

@[simp] theorem row_173 : allRows[173]? = some (RowKind.split 5 "00100" 4 "0010") := by
  decide

@[simp] theorem row_174 : allRows[174]? = some (RowKind.split 5 "00100" 4 "0100") := by
  decide

@[simp] theorem row_176 : allRows[176]? = some (RowKind.split 5 "00100" 4 "1001") := by
  decide

@[simp] theorem row_178 : allRows[178]? = some (RowKind.split 5 "00101" 4 "0010") := by
  decide

@[simp] theorem row_179 : allRows[179]? = some (RowKind.split 5 "00101" 4 "0100") := by
  decide

@[simp] theorem row_182 : allRows[182]? = some (RowKind.split 5 "00101" 4 "1010") := by
  decide

@[simp] theorem row_194 : allRows[194]? = some (RowKind.split 5 "10010" 4 "0100") := by
  decide

@[simp] theorem row_198 : allRows[198]? = some (RowKind.split 5 "10100" 4 "0010") := by
  decide

@[simp] theorem row_199 : allRows[199]? = some (RowKind.split 5 "10100" 4 "0100") := by
  decide

@[simp] theorem row_204 : allRows[204]? = some (RowKind.split 5 "10101" 4 "0100") := by
  decide

@[simp] theorem row_205 : allRows[205]? = some (RowKind.split 5 "10101" 4 "0101") := by
  decide

@[simp] theorem row_206 : allRows[206]? = some (RowKind.split 5 "10101" 4 "1001") := by
  decide

@[simp] theorem row_207 : allRows[207]? = some (RowKind.split 5 "10101" 4 "1010") := by
  decide

@[simp] theorem row_209 : allRows[209]? = some (RowKind.split 6 "001001" 3 "010") := by
  decide

@[simp] theorem row_213 : allRows[213]? = some (RowKind.split 6 "001010" 3 "010") := by
  decide

@[simp] theorem row_221 : allRows[221]? = some (RowKind.split 6 "010100" 3 "010") := by
  decide

@[simp] theorem row_222 : allRows[222]? = some (RowKind.split 6 "010100" 3 "100") := by
  decide

@[simp] theorem row_223 : allRows[223]? = some (RowKind.split 6 "010100" 3 "101") := by
  decide

@[simp] theorem row_224 : allRows[224]? = some (RowKind.split 6 "010101" 3 "001") := by
  decide

@[simp] theorem row_225 : allRows[225]? = some (RowKind.split 6 "010101" 3 "010") := by
  decide

@[simp] theorem row_226 : allRows[226]? = some (RowKind.split 6 "010101" 3 "100") := by
  decide

@[simp] theorem row_229 : allRows[229]? = some (RowKind.split 6 "100100" 3 "010") := by
  decide

@[simp] theorem row_230 : allRows[230]? = some (RowKind.split 6 "100100" 3 "100") := by
  decide

@[simp] theorem row_233 : allRows[233]? = some (RowKind.split 6 "100101" 3 "010") := by
  decide

@[simp] theorem row_234 : allRows[234]? = some (RowKind.split 6 "100101" 3 "100") := by
  decide

@[simp] theorem row_237 : allRows[237]? = some (RowKind.split 6 "101001" 3 "010") := by
  decide

@[simp] theorem row_241 : allRows[241]? = some (RowKind.split 6 "101010" 3 "010") := by
  decide

@[simp] theorem row_245 : allRows[245]? = some (RowKind.split 7 "0010010" 2 "01") := by
  decide

@[simp] theorem row_247 : allRows[247]? = some (RowKind.split 7 "0010100" 2 "00") := by
  decide

@[simp] theorem row_248 : allRows[248]? = some (RowKind.split 7 "0010100" 2 "01") := by
  decide

@[simp] theorem row_249 : allRows[249]? = some (RowKind.split 7 "0010100" 2 "10") := by
  decide

@[simp] theorem row_250 : allRows[250]? = some (RowKind.split 7 "0010101" 2 "00") := by
  decide

@[simp] theorem row_251 : allRows[251]? = some (RowKind.split 7 "0010101" 2 "01") := by
  decide

@[simp] theorem row_252 : allRows[252]? = some (RowKind.split 7 "0010101" 2 "10") := by
  decide

@[simp] theorem row_253 : allRows[253]? = some (RowKind.split 7 "0100100" 2 "00") := by
  decide

@[simp] theorem row_254 : allRows[254]? = some (RowKind.split 7 "0100100" 2 "01") := by
  decide

@[simp] theorem row_255 : allRows[255]? = some (RowKind.split 7 "0100100" 2 "10") := by
  decide

@[simp] theorem row_258 : allRows[258]? = some (RowKind.split 7 "0100101" 2 "10") := by
  decide

@[simp] theorem row_266 : allRows[266]? = some (RowKind.split 7 "1001001" 2 "01") := by
  decide

@[simp] theorem row_269 : allRows[269]? = some (RowKind.split 7 "1001010" 2 "01") := by
  decide

@[simp] theorem row_272 : allRows[272]? = some (RowKind.split 7 "1010010" 2 "01") := by
  decide

@[simp] theorem row_275 : allRows[275]? = some (RowKind.split 7 "1010100" 2 "01") := by
  decide

@[simp] theorem row_276 : allRows[276]? = some (RowKind.split 7 "1010100" 2 "10") := by
  decide

@[simp] theorem prefix14_00100100100100_4 : prefixOf "00100100100100" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00100100100100_1 : suffixFrom "00100100100100" 1 = "0100100100100" := by
  decide

@[simp] theorem prefix14_00100100100101_4 : prefixOf "00100100100101" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00100100100101_1 : suffixFrom "00100100100101" 1 = "0100100100101" := by
  decide

@[simp] theorem prefix14_00100100101001_4 : prefixOf "00100100101001" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00100100101001_1 : suffixFrom "00100100101001" 1 = "0100100101001" := by
  decide

@[simp] theorem prefix14_00100100101010_4 : prefixOf "00100100101010" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00100100101010_1 : suffixFrom "00100100101010" 1 = "0100100101010" := by
  decide

@[simp] theorem prefix14_00100101001001_4 : prefixOf "00100101001001" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00100101001001_1 : suffixFrom "00100101001001" 1 = "0100101001001" := by
  decide

@[simp] theorem prefix14_00100101001010_4 : prefixOf "00100101001010" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00100101001010_1 : suffixFrom "00100101001010" 1 = "0100101001010" := by
  decide

@[simp] theorem prefix14_00100101010010_4 : prefixOf "00100101010010" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00100101010010_1 : suffixFrom "00100101010010" 1 = "0100101010010" := by
  decide

@[simp] theorem prefix14_00100101010100_4 : prefixOf "00100101010100" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00100101010100_1 : suffixFrom "00100101010100" 1 = "0100101010100" := by
  decide

@[simp] theorem prefix14_00100101010101_4 : prefixOf "00100101010101" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00100101010101_1 : suffixFrom "00100101010101" 1 = "0100101010101" := by
  decide

@[simp] theorem prefix14_00101001001001_4 : prefixOf "00101001001001" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101001001001_1 : suffixFrom "00101001001001" 1 = "0101001001001" := by
  decide

@[simp] theorem prefix14_00101001001010_4 : prefixOf "00101001001010" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101001001010_1 : suffixFrom "00101001001010" 1 = "0101001001010" := by
  decide

@[simp] theorem prefix14_00101001010010_4 : prefixOf "00101001010010" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101001010010_1 : suffixFrom "00101001010010" 1 = "0101001010010" := by
  decide

@[simp] theorem prefix14_00101001010100_4 : prefixOf "00101001010100" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101001010100_1 : suffixFrom "00101001010100" 1 = "0101001010100" := by
  decide

@[simp] theorem prefix14_00101001010101_4 : prefixOf "00101001010101" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101001010101_1 : suffixFrom "00101001010101" 1 = "0101001010101" := by
  decide

@[simp] theorem prefix14_00101010010010_4 : prefixOf "00101010010010" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101010010010_1 : suffixFrom "00101010010010" 1 = "0101010010010" := by
  decide

@[simp] theorem prefix14_00101010010100_4 : prefixOf "00101010010100" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101010010100_1 : suffixFrom "00101010010100" 1 = "0101010010100" := by
  decide

@[simp] theorem prefix14_00101010010101_4 : prefixOf "00101010010101" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101010010101_1 : suffixFrom "00101010010101" 1 = "0101010010101" := by
  decide

@[simp] theorem prefix14_00101010100100_4 : prefixOf "00101010100100" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101010100100_1 : suffixFrom "00101010100100" 1 = "0101010100100" := by
  decide

@[simp] theorem prefix14_00101010100101_4 : prefixOf "00101010100101" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101010100101_1 : suffixFrom "00101010100101" 1 = "0101010100101" := by
  decide

@[simp] theorem prefix14_00101010101001_4 : prefixOf "00101010101001" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101010101001_1 : suffixFrom "00101010101001" 1 = "0101010101001" := by
  decide

@[simp] theorem prefix14_00101010101010_4 : prefixOf "00101010101010" 4 = "0010" := by
  decide

@[simp] theorem suffix14_00101010101010_1 : suffixFrom "00101010101010" 1 = "0101010101010" := by
  decide

@[simp] theorem prefix14_01001001001001_4 : prefixOf "01001001001001" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001001001001_1 : suffixFrom "01001001001001" 1 = "1001001001001" := by
  decide

@[simp] theorem prefix14_01001001001010_4 : prefixOf "01001001001010" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001001001010_1 : suffixFrom "01001001001010" 1 = "1001001001010" := by
  decide

@[simp] theorem prefix14_01001001010010_4 : prefixOf "01001001010010" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001001010010_1 : suffixFrom "01001001010010" 1 = "1001001010010" := by
  decide

@[simp] theorem prefix14_01001001010100_4 : prefixOf "01001001010100" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001001010100_1 : suffixFrom "01001001010100" 1 = "1001001010100" := by
  decide

@[simp] theorem prefix14_01001001010101_4 : prefixOf "01001001010101" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001001010101_1 : suffixFrom "01001001010101" 1 = "1001001010101" := by
  decide

@[simp] theorem prefix14_01001010010010_4 : prefixOf "01001010010010" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001010010010_1 : suffixFrom "01001010010010" 1 = "1001010010010" := by
  decide

@[simp] theorem prefix14_01001010010100_4 : prefixOf "01001010010100" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001010010100_1 : suffixFrom "01001010010100" 1 = "1001010010100" := by
  decide

@[simp] theorem prefix14_01001010010101_4 : prefixOf "01001010010101" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001010010101_1 : suffixFrom "01001010010101" 1 = "1001010010101" := by
  decide

@[simp] theorem prefix14_01001010100100_4 : prefixOf "01001010100100" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001010100100_1 : suffixFrom "01001010100100" 1 = "1001010100100" := by
  decide

@[simp] theorem prefix14_01001010100101_4 : prefixOf "01001010100101" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001010100101_1 : suffixFrom "01001010100101" 1 = "1001010100101" := by
  decide

@[simp] theorem prefix14_01001010101001_4 : prefixOf "01001010101001" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001010101001_1 : suffixFrom "01001010101001" 1 = "1001010101001" := by
  decide

@[simp] theorem prefix14_01001010101010_4 : prefixOf "01001010101010" 4 = "0100" := by
  decide

@[simp] theorem suffix14_01001010101010_1 : suffixFrom "01001010101010" 1 = "1001010101010" := by
  decide

@[simp] theorem prefix14_01010010010010_4 : prefixOf "01010010010010" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010010010010_1 : suffixFrom "01010010010010" 1 = "1010010010010" := by
  decide

@[simp] theorem prefix14_01010010010100_4 : prefixOf "01010010010100" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010010010100_1 : suffixFrom "01010010010100" 1 = "1010010010100" := by
  decide

@[simp] theorem prefix14_01010010010101_4 : prefixOf "01010010010101" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010010010101_1 : suffixFrom "01010010010101" 1 = "1010010010101" := by
  decide

@[simp] theorem prefix14_01010010100100_4 : prefixOf "01010010100100" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010010100100_1 : suffixFrom "01010010100100" 1 = "1010010100100" := by
  decide

@[simp] theorem prefix14_01010010100101_4 : prefixOf "01010010100101" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010010100101_1 : suffixFrom "01010010100101" 1 = "1010010100101" := by
  decide

@[simp] theorem prefix14_01010010101001_4 : prefixOf "01010010101001" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010010101001_1 : suffixFrom "01010010101001" 1 = "1010010101001" := by
  decide

@[simp] theorem prefix14_01010010101010_4 : prefixOf "01010010101010" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010010101010_1 : suffixFrom "01010010101010" 1 = "1010010101010" := by
  decide

@[simp] theorem prefix14_01010100100100_4 : prefixOf "01010100100100" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010100100100_1 : suffixFrom "01010100100100" 1 = "1010100100100" := by
  decide

@[simp] theorem prefix14_01010100100101_4 : prefixOf "01010100100101" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010100100101_1 : suffixFrom "01010100100101" 1 = "1010100100101" := by
  decide

@[simp] theorem prefix14_01010100101001_4 : prefixOf "01010100101001" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010100101001_1 : suffixFrom "01010100101001" 1 = "1010100101001" := by
  decide

@[simp] theorem prefix14_01010100101010_4 : prefixOf "01010100101010" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010100101010_1 : suffixFrom "01010100101010" 1 = "1010100101010" := by
  decide

@[simp] theorem prefix14_01010101001001_4 : prefixOf "01010101001001" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010101001001_1 : suffixFrom "01010101001001" 1 = "1010101001001" := by
  decide

@[simp] theorem prefix14_01010101001010_4 : prefixOf "01010101001010" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010101001010_1 : suffixFrom "01010101001010" 1 = "1010101001010" := by
  decide

@[simp] theorem prefix14_01010101010010_4 : prefixOf "01010101010010" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010101010010_1 : suffixFrom "01010101010010" 1 = "1010101010010" := by
  decide

@[simp] theorem prefix14_01010101010100_4 : prefixOf "01010101010100" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010101010100_1 : suffixFrom "01010101010100" 1 = "1010101010100" := by
  decide

@[simp] theorem prefix14_01010101010101_4 : prefixOf "01010101010101" 4 = "0101" := by
  decide

@[simp] theorem suffix14_01010101010101_1 : suffixFrom "01010101010101" 1 = "1010101010101" := by
  decide

@[simp] theorem prefix14_10010010010010_4 : prefixOf "10010010010010" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010010010010_1 : suffixFrom "10010010010010" 1 = "0010010010010" := by
  decide

@[simp] theorem prefix14_10010010010100_4 : prefixOf "10010010010100" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010010010100_1 : suffixFrom "10010010010100" 1 = "0010010010100" := by
  decide

@[simp] theorem prefix14_10010010010101_4 : prefixOf "10010010010101" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010010010101_1 : suffixFrom "10010010010101" 1 = "0010010010101" := by
  decide

@[simp] theorem prefix14_10010010100100_4 : prefixOf "10010010100100" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010010100100_1 : suffixFrom "10010010100100" 1 = "0010010100100" := by
  decide

@[simp] theorem prefix14_10010010100101_4 : prefixOf "10010010100101" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010010100101_1 : suffixFrom "10010010100101" 1 = "0010010100101" := by
  decide

@[simp] theorem prefix14_10010010101001_4 : prefixOf "10010010101001" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010010101001_1 : suffixFrom "10010010101001" 1 = "0010010101001" := by
  decide

@[simp] theorem prefix14_10010010101010_4 : prefixOf "10010010101010" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010010101010_1 : suffixFrom "10010010101010" 1 = "0010010101010" := by
  decide

@[simp] theorem prefix14_10010100100100_4 : prefixOf "10010100100100" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010100100100_1 : suffixFrom "10010100100100" 1 = "0010100100100" := by
  decide

@[simp] theorem prefix14_10010100100101_4 : prefixOf "10010100100101" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010100100101_1 : suffixFrom "10010100100101" 1 = "0010100100101" := by
  decide

@[simp] theorem prefix14_10010100101001_4 : prefixOf "10010100101001" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010100101001_1 : suffixFrom "10010100101001" 1 = "0010100101001" := by
  decide

@[simp] theorem prefix14_10010100101010_4 : prefixOf "10010100101010" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010100101010_1 : suffixFrom "10010100101010" 1 = "0010100101010" := by
  decide

@[simp] theorem prefix14_10010101001001_4 : prefixOf "10010101001001" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010101001001_1 : suffixFrom "10010101001001" 1 = "0010101001001" := by
  decide

@[simp] theorem prefix14_10010101001010_4 : prefixOf "10010101001010" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010101001010_1 : suffixFrom "10010101001010" 1 = "0010101001010" := by
  decide

@[simp] theorem prefix14_10010101010010_4 : prefixOf "10010101010010" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010101010010_1 : suffixFrom "10010101010010" 1 = "0010101010010" := by
  decide

@[simp] theorem prefix14_10010101010100_4 : prefixOf "10010101010100" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010101010100_1 : suffixFrom "10010101010100" 1 = "0010101010100" := by
  decide

@[simp] theorem prefix14_10010101010101_4 : prefixOf "10010101010101" 4 = "1001" := by
  decide

@[simp] theorem suffix14_10010101010101_1 : suffixFrom "10010101010101" 1 = "0010101010101" := by
  decide

@[simp] theorem prefix14_10100100100100_4 : prefixOf "10100100100100" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10100100100100_1 : suffixFrom "10100100100100" 1 = "0100100100100" := by
  decide

@[simp] theorem prefix14_10100100100101_4 : prefixOf "10100100100101" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10100100100101_1 : suffixFrom "10100100100101" 1 = "0100100100101" := by
  decide

@[simp] theorem prefix14_10100100101001_4 : prefixOf "10100100101001" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10100100101001_1 : suffixFrom "10100100101001" 1 = "0100100101001" := by
  decide

@[simp] theorem prefix14_10100100101010_4 : prefixOf "10100100101010" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10100100101010_1 : suffixFrom "10100100101010" 1 = "0100100101010" := by
  decide

@[simp] theorem prefix14_10100101001001_4 : prefixOf "10100101001001" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10100101001001_1 : suffixFrom "10100101001001" 1 = "0100101001001" := by
  decide

@[simp] theorem prefix14_10100101001010_4 : prefixOf "10100101001010" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10100101001010_1 : suffixFrom "10100101001010" 1 = "0100101001010" := by
  decide

@[simp] theorem prefix14_10100101010010_4 : prefixOf "10100101010010" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10100101010010_1 : suffixFrom "10100101010010" 1 = "0100101010010" := by
  decide

@[simp] theorem prefix14_10100101010100_4 : prefixOf "10100101010100" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10100101010100_1 : suffixFrom "10100101010100" 1 = "0100101010100" := by
  decide

@[simp] theorem prefix14_10100101010101_4 : prefixOf "10100101010101" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10100101010101_1 : suffixFrom "10100101010101" 1 = "0100101010101" := by
  decide

@[simp] theorem prefix14_10101001001001_4 : prefixOf "10101001001001" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101001001001_1 : suffixFrom "10101001001001" 1 = "0101001001001" := by
  decide

@[simp] theorem prefix14_10101001001010_4 : prefixOf "10101001001010" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101001001010_1 : suffixFrom "10101001001010" 1 = "0101001001010" := by
  decide

@[simp] theorem prefix14_10101001010010_4 : prefixOf "10101001010010" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101001010010_1 : suffixFrom "10101001010010" 1 = "0101001010010" := by
  decide

@[simp] theorem prefix14_10101001010100_4 : prefixOf "10101001010100" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101001010100_1 : suffixFrom "10101001010100" 1 = "0101001010100" := by
  decide

@[simp] theorem prefix14_10101001010101_4 : prefixOf "10101001010101" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101001010101_1 : suffixFrom "10101001010101" 1 = "0101001010101" := by
  decide

@[simp] theorem prefix14_10101010010010_4 : prefixOf "10101010010010" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101010010010_1 : suffixFrom "10101010010010" 1 = "0101010010010" := by
  decide

@[simp] theorem prefix14_10101010010100_4 : prefixOf "10101010010100" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101010010100_1 : suffixFrom "10101010010100" 1 = "0101010010100" := by
  decide

@[simp] theorem prefix14_10101010010101_4 : prefixOf "10101010010101" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101010010101_1 : suffixFrom "10101010010101" 1 = "0101010010101" := by
  decide

@[simp] theorem prefix14_10101010100100_4 : prefixOf "10101010100100" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101010100100_1 : suffixFrom "10101010100100" 1 = "0101010100100" := by
  decide

@[simp] theorem prefix14_10101010100101_4 : prefixOf "10101010100101" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101010100101_1 : suffixFrom "10101010100101" 1 = "0101010100101" := by
  decide

@[simp] theorem prefix14_10101010101001_4 : prefixOf "10101010101001" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101010101001_1 : suffixFrom "10101010101001" 1 = "0101010101001" := by
  decide

@[simp] theorem prefix14_10101010101010_4 : prefixOf "10101010101010" 4 = "1010" := by
  decide

@[simp] theorem suffix14_10101010101010_1 : suffixFrom "10101010101010" 1 = "0101010101010" := by
  decide

@[simp] theorem prefix14_00100100100100_1 : prefixOf "00100100100100" 1 = "0" := by
  decide

@[simp] theorem prefix14_00100100100100_2 : prefixOf "00100100100100" 2 = "00" := by
  decide

@[simp] theorem prefix14_00100100100100_3 : prefixOf "00100100100100" 3 = "001" := by
  decide

@[simp] theorem prefix14_00100100100100_5 : prefixOf "00100100100100" 5 = "00100" := by
  decide

@[simp] theorem prefix14_00100100100100_6 : prefixOf "00100100100100" 6 = "001001" := by
  decide

@[simp] theorem prefix14_00100100100100_7 : prefixOf "00100100100100" 7 = "0010010" := by
  decide

@[simp] theorem prefix14_00100100100100_8 : prefixOf "00100100100100" 8 = "00100100" := by
  decide

@[simp] theorem prefix14_00100100100100_9 : prefixOf "00100100100100" 9 = "001001001" := by
  decide

@[simp] theorem prefix14_00100100100100_10 : prefixOf "00100100100100" 10 = "0010010010" := by
  decide

@[simp] theorem prefix14_00100100100100_11 : prefixOf "00100100100100" 11 = "00100100100" := by
  decide

@[simp] theorem prefix14_00100100100100_12 : prefixOf "00100100100100" 12 = "001001001001" := by
  decide

@[simp] theorem prefix14_00100100100100_13 : prefixOf "00100100100100" 13 = "0010010010010" := by
  decide

@[simp] theorem prefix14_00100100100100_14 : prefixOf "00100100100100" 14 = "00100100100100" := by
  decide

@[simp] theorem suffix14_00100100100100_7 : suffixFrom "00100100100100" 7 = "0100100" := by
  decide

@[simp] theorem suffix14_00100100100100_8 : suffixFrom "00100100100100" 8 = "100100" := by
  decide

@[simp] theorem suffix14_00100100100100_9 : suffixFrom "00100100100100" 9 = "00100" := by
  decide

@[simp] theorem suffix14_00100100100100_10 : suffixFrom "00100100100100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_00100100100100_11 : suffixFrom "00100100100100" 11 = "100" := by
  decide

@[simp] theorem suffix14_00100100100100_12 : suffixFrom "00100100100100" 12 = "00" := by
  decide

@[simp] theorem prefix14_00100100100101_1 : prefixOf "00100100100101" 1 = "0" := by
  decide

@[simp] theorem prefix14_00100100100101_2 : prefixOf "00100100100101" 2 = "00" := by
  decide

@[simp] theorem prefix14_00100100100101_3 : prefixOf "00100100100101" 3 = "001" := by
  decide

@[simp] theorem prefix14_00100100100101_5 : prefixOf "00100100100101" 5 = "00100" := by
  decide

@[simp] theorem prefix14_00100100100101_6 : prefixOf "00100100100101" 6 = "001001" := by
  decide

@[simp] theorem prefix14_00100100100101_7 : prefixOf "00100100100101" 7 = "0010010" := by
  decide

@[simp] theorem prefix14_00100100100101_8 : prefixOf "00100100100101" 8 = "00100100" := by
  decide

@[simp] theorem prefix14_00100100100101_9 : prefixOf "00100100100101" 9 = "001001001" := by
  decide

@[simp] theorem prefix14_00100100100101_10 : prefixOf "00100100100101" 10 = "0010010010" := by
  decide

@[simp] theorem prefix14_00100100100101_11 : prefixOf "00100100100101" 11 = "00100100100" := by
  decide

@[simp] theorem prefix14_00100100100101_12 : prefixOf "00100100100101" 12 = "001001001001" := by
  decide

@[simp] theorem prefix14_00100100100101_13 : prefixOf "00100100100101" 13 = "0010010010010" := by
  decide

@[simp] theorem prefix14_00100100100101_14 : prefixOf "00100100100101" 14 = "00100100100101" := by
  decide

@[simp] theorem suffix14_00100100100101_7 : suffixFrom "00100100100101" 7 = "0100101" := by
  decide

@[simp] theorem suffix14_00100100100101_8 : suffixFrom "00100100100101" 8 = "100101" := by
  decide

@[simp] theorem suffix14_00100100100101_9 : suffixFrom "00100100100101" 9 = "00101" := by
  decide

@[simp] theorem suffix14_00100100100101_10 : suffixFrom "00100100100101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_00100100100101_11 : suffixFrom "00100100100101" 11 = "101" := by
  decide

@[simp] theorem suffix14_00100100100101_12 : suffixFrom "00100100100101" 12 = "01" := by
  decide

@[simp] theorem prefix14_00100100101001_1 : prefixOf "00100100101001" 1 = "0" := by
  decide

@[simp] theorem prefix14_00100100101001_2 : prefixOf "00100100101001" 2 = "00" := by
  decide

@[simp] theorem prefix14_00100100101001_3 : prefixOf "00100100101001" 3 = "001" := by
  decide

@[simp] theorem prefix14_00100100101001_5 : prefixOf "00100100101001" 5 = "00100" := by
  decide

@[simp] theorem prefix14_00100100101001_6 : prefixOf "00100100101001" 6 = "001001" := by
  decide

@[simp] theorem prefix14_00100100101001_7 : prefixOf "00100100101001" 7 = "0010010" := by
  decide

@[simp] theorem prefix14_00100100101001_8 : prefixOf "00100100101001" 8 = "00100100" := by
  decide

@[simp] theorem prefix14_00100100101001_9 : prefixOf "00100100101001" 9 = "001001001" := by
  decide

@[simp] theorem prefix14_00100100101001_10 : prefixOf "00100100101001" 10 = "0010010010" := by
  decide

@[simp] theorem prefix14_00100100101001_11 : prefixOf "00100100101001" 11 = "00100100101" := by
  decide

@[simp] theorem prefix14_00100100101001_12 : prefixOf "00100100101001" 12 = "001001001010" := by
  decide

@[simp] theorem prefix14_00100100101001_13 : prefixOf "00100100101001" 13 = "0010010010100" := by
  decide

@[simp] theorem prefix14_00100100101001_14 : prefixOf "00100100101001" 14 = "00100100101001" := by
  decide

@[simp] theorem suffix14_00100100101001_7 : suffixFrom "00100100101001" 7 = "0101001" := by
  decide

@[simp] theorem suffix14_00100100101001_8 : suffixFrom "00100100101001" 8 = "101001" := by
  decide

@[simp] theorem suffix14_00100100101001_9 : suffixFrom "00100100101001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_00100100101001_10 : suffixFrom "00100100101001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_00100100101001_11 : suffixFrom "00100100101001" 11 = "001" := by
  decide

@[simp] theorem suffix14_00100100101001_12 : suffixFrom "00100100101001" 12 = "01" := by
  decide

@[simp] theorem prefix14_00100100101010_1 : prefixOf "00100100101010" 1 = "0" := by
  decide

@[simp] theorem prefix14_00100100101010_2 : prefixOf "00100100101010" 2 = "00" := by
  decide

@[simp] theorem prefix14_00100100101010_3 : prefixOf "00100100101010" 3 = "001" := by
  decide

@[simp] theorem prefix14_00100100101010_5 : prefixOf "00100100101010" 5 = "00100" := by
  decide

@[simp] theorem prefix14_00100100101010_6 : prefixOf "00100100101010" 6 = "001001" := by
  decide

@[simp] theorem prefix14_00100100101010_7 : prefixOf "00100100101010" 7 = "0010010" := by
  decide

@[simp] theorem prefix14_00100100101010_8 : prefixOf "00100100101010" 8 = "00100100" := by
  decide

@[simp] theorem prefix14_00100100101010_9 : prefixOf "00100100101010" 9 = "001001001" := by
  decide

@[simp] theorem prefix14_00100100101010_10 : prefixOf "00100100101010" 10 = "0010010010" := by
  decide

@[simp] theorem prefix14_00100100101010_11 : prefixOf "00100100101010" 11 = "00100100101" := by
  decide

@[simp] theorem prefix14_00100100101010_12 : prefixOf "00100100101010" 12 = "001001001010" := by
  decide

@[simp] theorem prefix14_00100100101010_13 : prefixOf "00100100101010" 13 = "0010010010101" := by
  decide

@[simp] theorem prefix14_00100100101010_14 : prefixOf "00100100101010" 14 = "00100100101010" := by
  decide

@[simp] theorem suffix14_00100100101010_7 : suffixFrom "00100100101010" 7 = "0101010" := by
  decide

@[simp] theorem suffix14_00100100101010_8 : suffixFrom "00100100101010" 8 = "101010" := by
  decide

@[simp] theorem suffix14_00100100101010_9 : suffixFrom "00100100101010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_00100100101010_10 : suffixFrom "00100100101010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_00100100101010_11 : suffixFrom "00100100101010" 11 = "010" := by
  decide

@[simp] theorem suffix14_00100100101010_12 : suffixFrom "00100100101010" 12 = "10" := by
  decide

@[simp] theorem prefix14_00100101001001_1 : prefixOf "00100101001001" 1 = "0" := by
  decide

@[simp] theorem prefix14_00100101001001_2 : prefixOf "00100101001001" 2 = "00" := by
  decide

@[simp] theorem prefix14_00100101001001_3 : prefixOf "00100101001001" 3 = "001" := by
  decide

@[simp] theorem prefix14_00100101001001_5 : prefixOf "00100101001001" 5 = "00100" := by
  decide

@[simp] theorem prefix14_00100101001001_6 : prefixOf "00100101001001" 6 = "001001" := by
  decide

@[simp] theorem prefix14_00100101001001_7 : prefixOf "00100101001001" 7 = "0010010" := by
  decide

@[simp] theorem prefix14_00100101001001_8 : prefixOf "00100101001001" 8 = "00100101" := by
  decide

@[simp] theorem prefix14_00100101001001_9 : prefixOf "00100101001001" 9 = "001001010" := by
  decide

@[simp] theorem prefix14_00100101001001_10 : prefixOf "00100101001001" 10 = "0010010100" := by
  decide

@[simp] theorem prefix14_00100101001001_11 : prefixOf "00100101001001" 11 = "00100101001" := by
  decide

@[simp] theorem prefix14_00100101001001_12 : prefixOf "00100101001001" 12 = "001001010010" := by
  decide

@[simp] theorem prefix14_00100101001001_13 : prefixOf "00100101001001" 13 = "0010010100100" := by
  decide

@[simp] theorem prefix14_00100101001001_14 : prefixOf "00100101001001" 14 = "00100101001001" := by
  decide

@[simp] theorem suffix14_00100101001001_7 : suffixFrom "00100101001001" 7 = "1001001" := by
  decide

@[simp] theorem suffix14_00100101001001_8 : suffixFrom "00100101001001" 8 = "001001" := by
  decide

@[simp] theorem suffix14_00100101001001_9 : suffixFrom "00100101001001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_00100101001001_10 : suffixFrom "00100101001001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_00100101001001_11 : suffixFrom "00100101001001" 11 = "001" := by
  decide

@[simp] theorem suffix14_00100101001001_12 : suffixFrom "00100101001001" 12 = "01" := by
  decide

@[simp] theorem prefix14_00100101001010_1 : prefixOf "00100101001010" 1 = "0" := by
  decide

@[simp] theorem prefix14_00100101001010_2 : prefixOf "00100101001010" 2 = "00" := by
  decide

@[simp] theorem prefix14_00100101001010_3 : prefixOf "00100101001010" 3 = "001" := by
  decide

@[simp] theorem prefix14_00100101001010_5 : prefixOf "00100101001010" 5 = "00100" := by
  decide

@[simp] theorem prefix14_00100101001010_6 : prefixOf "00100101001010" 6 = "001001" := by
  decide

@[simp] theorem prefix14_00100101001010_7 : prefixOf "00100101001010" 7 = "0010010" := by
  decide

@[simp] theorem prefix14_00100101001010_8 : prefixOf "00100101001010" 8 = "00100101" := by
  decide

@[simp] theorem prefix14_00100101001010_9 : prefixOf "00100101001010" 9 = "001001010" := by
  decide

@[simp] theorem prefix14_00100101001010_10 : prefixOf "00100101001010" 10 = "0010010100" := by
  decide

@[simp] theorem prefix14_00100101001010_11 : prefixOf "00100101001010" 11 = "00100101001" := by
  decide

@[simp] theorem prefix14_00100101001010_12 : prefixOf "00100101001010" 12 = "001001010010" := by
  decide

@[simp] theorem prefix14_00100101001010_13 : prefixOf "00100101001010" 13 = "0010010100101" := by
  decide

@[simp] theorem prefix14_00100101001010_14 : prefixOf "00100101001010" 14 = "00100101001010" := by
  decide

@[simp] theorem suffix14_00100101001010_7 : suffixFrom "00100101001010" 7 = "1001010" := by
  decide

@[simp] theorem suffix14_00100101001010_8 : suffixFrom "00100101001010" 8 = "001010" := by
  decide

@[simp] theorem suffix14_00100101001010_9 : suffixFrom "00100101001010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_00100101001010_10 : suffixFrom "00100101001010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_00100101001010_11 : suffixFrom "00100101001010" 11 = "010" := by
  decide

@[simp] theorem suffix14_00100101001010_12 : suffixFrom "00100101001010" 12 = "10" := by
  decide

@[simp] theorem prefix14_00100101010010_1 : prefixOf "00100101010010" 1 = "0" := by
  decide

@[simp] theorem prefix14_00100101010010_2 : prefixOf "00100101010010" 2 = "00" := by
  decide

@[simp] theorem prefix14_00100101010010_3 : prefixOf "00100101010010" 3 = "001" := by
  decide

@[simp] theorem prefix14_00100101010010_5 : prefixOf "00100101010010" 5 = "00100" := by
  decide

@[simp] theorem prefix14_00100101010010_6 : prefixOf "00100101010010" 6 = "001001" := by
  decide

@[simp] theorem prefix14_00100101010010_7 : prefixOf "00100101010010" 7 = "0010010" := by
  decide

@[simp] theorem prefix14_00100101010010_8 : prefixOf "00100101010010" 8 = "00100101" := by
  decide

@[simp] theorem prefix14_00100101010010_9 : prefixOf "00100101010010" 9 = "001001010" := by
  decide

@[simp] theorem prefix14_00100101010010_10 : prefixOf "00100101010010" 10 = "0010010101" := by
  decide

@[simp] theorem prefix14_00100101010010_11 : prefixOf "00100101010010" 11 = "00100101010" := by
  decide

@[simp] theorem prefix14_00100101010010_12 : prefixOf "00100101010010" 12 = "001001010100" := by
  decide

@[simp] theorem prefix14_00100101010010_13 : prefixOf "00100101010010" 13 = "0010010101001" := by
  decide

@[simp] theorem prefix14_00100101010010_14 : prefixOf "00100101010010" 14 = "00100101010010" := by
  decide

@[simp] theorem suffix14_00100101010010_7 : suffixFrom "00100101010010" 7 = "1010010" := by
  decide

@[simp] theorem suffix14_00100101010010_8 : suffixFrom "00100101010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_00100101010010_9 : suffixFrom "00100101010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_00100101010010_10 : suffixFrom "00100101010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_00100101010010_11 : suffixFrom "00100101010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_00100101010010_12 : suffixFrom "00100101010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_00100101010100_1 : prefixOf "00100101010100" 1 = "0" := by
  decide

@[simp] theorem prefix14_00100101010100_2 : prefixOf "00100101010100" 2 = "00" := by
  decide

@[simp] theorem prefix14_00100101010100_3 : prefixOf "00100101010100" 3 = "001" := by
  decide

@[simp] theorem prefix14_00100101010100_5 : prefixOf "00100101010100" 5 = "00100" := by
  decide

@[simp] theorem prefix14_00100101010100_6 : prefixOf "00100101010100" 6 = "001001" := by
  decide

@[simp] theorem prefix14_00100101010100_7 : prefixOf "00100101010100" 7 = "0010010" := by
  decide

@[simp] theorem prefix14_00100101010100_8 : prefixOf "00100101010100" 8 = "00100101" := by
  decide

@[simp] theorem prefix14_00100101010100_9 : prefixOf "00100101010100" 9 = "001001010" := by
  decide

@[simp] theorem prefix14_00100101010100_10 : prefixOf "00100101010100" 10 = "0010010101" := by
  decide

@[simp] theorem prefix14_00100101010100_11 : prefixOf "00100101010100" 11 = "00100101010" := by
  decide

@[simp] theorem prefix14_00100101010100_12 : prefixOf "00100101010100" 12 = "001001010101" := by
  decide

@[simp] theorem prefix14_00100101010100_13 : prefixOf "00100101010100" 13 = "0010010101010" := by
  decide

@[simp] theorem prefix14_00100101010100_14 : prefixOf "00100101010100" 14 = "00100101010100" := by
  decide

@[simp] theorem suffix14_00100101010100_7 : suffixFrom "00100101010100" 7 = "1010100" := by
  decide

@[simp] theorem suffix14_00100101010100_8 : suffixFrom "00100101010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_00100101010100_9 : suffixFrom "00100101010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_00100101010100_10 : suffixFrom "00100101010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_00100101010100_11 : suffixFrom "00100101010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_00100101010100_12 : suffixFrom "00100101010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_00100101010101_1 : prefixOf "00100101010101" 1 = "0" := by
  decide

@[simp] theorem prefix14_00100101010101_2 : prefixOf "00100101010101" 2 = "00" := by
  decide

@[simp] theorem prefix14_00100101010101_3 : prefixOf "00100101010101" 3 = "001" := by
  decide

@[simp] theorem prefix14_00100101010101_5 : prefixOf "00100101010101" 5 = "00100" := by
  decide

@[simp] theorem prefix14_00100101010101_6 : prefixOf "00100101010101" 6 = "001001" := by
  decide

@[simp] theorem prefix14_00100101010101_7 : prefixOf "00100101010101" 7 = "0010010" := by
  decide

@[simp] theorem prefix14_00100101010101_8 : prefixOf "00100101010101" 8 = "00100101" := by
  decide

@[simp] theorem prefix14_00100101010101_9 : prefixOf "00100101010101" 9 = "001001010" := by
  decide

@[simp] theorem prefix14_00100101010101_10 : prefixOf "00100101010101" 10 = "0010010101" := by
  decide

@[simp] theorem prefix14_00100101010101_11 : prefixOf "00100101010101" 11 = "00100101010" := by
  decide

@[simp] theorem prefix14_00100101010101_12 : prefixOf "00100101010101" 12 = "001001010101" := by
  decide

@[simp] theorem prefix14_00100101010101_13 : prefixOf "00100101010101" 13 = "0010010101010" := by
  decide

@[simp] theorem prefix14_00100101010101_14 : prefixOf "00100101010101" 14 = "00100101010101" := by
  decide

@[simp] theorem suffix14_00100101010101_7 : suffixFrom "00100101010101" 7 = "1010101" := by
  decide

@[simp] theorem suffix14_00100101010101_8 : suffixFrom "00100101010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_00100101010101_9 : suffixFrom "00100101010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_00100101010101_10 : suffixFrom "00100101010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_00100101010101_11 : suffixFrom "00100101010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_00100101010101_12 : suffixFrom "00100101010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_00101001001001_1 : prefixOf "00101001001001" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101001001001_2 : prefixOf "00101001001001" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101001001001_3 : prefixOf "00101001001001" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101001001001_5 : prefixOf "00101001001001" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101001001001_6 : prefixOf "00101001001001" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101001001001_7 : prefixOf "00101001001001" 7 = "0010100" := by
  decide

@[simp] theorem prefix14_00101001001001_8 : prefixOf "00101001001001" 8 = "00101001" := by
  decide

@[simp] theorem prefix14_00101001001001_9 : prefixOf "00101001001001" 9 = "001010010" := by
  decide

@[simp] theorem prefix14_00101001001001_10 : prefixOf "00101001001001" 10 = "0010100100" := by
  decide

@[simp] theorem prefix14_00101001001001_11 : prefixOf "00101001001001" 11 = "00101001001" := by
  decide

@[simp] theorem prefix14_00101001001001_12 : prefixOf "00101001001001" 12 = "001010010010" := by
  decide

@[simp] theorem prefix14_00101001001001_13 : prefixOf "00101001001001" 13 = "0010100100100" := by
  decide

@[simp] theorem prefix14_00101001001001_14 : prefixOf "00101001001001" 14 = "00101001001001" := by
  decide

@[simp] theorem suffix14_00101001001001_7 : suffixFrom "00101001001001" 7 = "1001001" := by
  decide

@[simp] theorem suffix14_00101001001001_8 : suffixFrom "00101001001001" 8 = "001001" := by
  decide

@[simp] theorem suffix14_00101001001001_9 : suffixFrom "00101001001001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_00101001001001_10 : suffixFrom "00101001001001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_00101001001001_11 : suffixFrom "00101001001001" 11 = "001" := by
  decide

@[simp] theorem suffix14_00101001001001_12 : suffixFrom "00101001001001" 12 = "01" := by
  decide

@[simp] theorem prefix14_00101001001010_1 : prefixOf "00101001001010" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101001001010_2 : prefixOf "00101001001010" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101001001010_3 : prefixOf "00101001001010" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101001001010_5 : prefixOf "00101001001010" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101001001010_6 : prefixOf "00101001001010" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101001001010_7 : prefixOf "00101001001010" 7 = "0010100" := by
  decide

@[simp] theorem prefix14_00101001001010_8 : prefixOf "00101001001010" 8 = "00101001" := by
  decide

@[simp] theorem prefix14_00101001001010_9 : prefixOf "00101001001010" 9 = "001010010" := by
  decide

@[simp] theorem prefix14_00101001001010_10 : prefixOf "00101001001010" 10 = "0010100100" := by
  decide

@[simp] theorem prefix14_00101001001010_11 : prefixOf "00101001001010" 11 = "00101001001" := by
  decide

@[simp] theorem prefix14_00101001001010_12 : prefixOf "00101001001010" 12 = "001010010010" := by
  decide

@[simp] theorem prefix14_00101001001010_13 : prefixOf "00101001001010" 13 = "0010100100101" := by
  decide

@[simp] theorem prefix14_00101001001010_14 : prefixOf "00101001001010" 14 = "00101001001010" := by
  decide

@[simp] theorem suffix14_00101001001010_7 : suffixFrom "00101001001010" 7 = "1001010" := by
  decide

@[simp] theorem suffix14_00101001001010_8 : suffixFrom "00101001001010" 8 = "001010" := by
  decide

@[simp] theorem suffix14_00101001001010_9 : suffixFrom "00101001001010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_00101001001010_10 : suffixFrom "00101001001010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_00101001001010_11 : suffixFrom "00101001001010" 11 = "010" := by
  decide

@[simp] theorem suffix14_00101001001010_12 : suffixFrom "00101001001010" 12 = "10" := by
  decide

@[simp] theorem prefix14_00101001010010_1 : prefixOf "00101001010010" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101001010010_2 : prefixOf "00101001010010" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101001010010_3 : prefixOf "00101001010010" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101001010010_5 : prefixOf "00101001010010" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101001010010_6 : prefixOf "00101001010010" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101001010010_7 : prefixOf "00101001010010" 7 = "0010100" := by
  decide

@[simp] theorem prefix14_00101001010010_8 : prefixOf "00101001010010" 8 = "00101001" := by
  decide

@[simp] theorem prefix14_00101001010010_9 : prefixOf "00101001010010" 9 = "001010010" := by
  decide

@[simp] theorem prefix14_00101001010010_10 : prefixOf "00101001010010" 10 = "0010100101" := by
  decide

@[simp] theorem prefix14_00101001010010_11 : prefixOf "00101001010010" 11 = "00101001010" := by
  decide

@[simp] theorem prefix14_00101001010010_12 : prefixOf "00101001010010" 12 = "001010010100" := by
  decide

@[simp] theorem prefix14_00101001010010_13 : prefixOf "00101001010010" 13 = "0010100101001" := by
  decide

@[simp] theorem prefix14_00101001010010_14 : prefixOf "00101001010010" 14 = "00101001010010" := by
  decide

@[simp] theorem suffix14_00101001010010_7 : suffixFrom "00101001010010" 7 = "1010010" := by
  decide

@[simp] theorem suffix14_00101001010010_8 : suffixFrom "00101001010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_00101001010010_9 : suffixFrom "00101001010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_00101001010010_10 : suffixFrom "00101001010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_00101001010010_11 : suffixFrom "00101001010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_00101001010010_12 : suffixFrom "00101001010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_00101001010100_1 : prefixOf "00101001010100" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101001010100_2 : prefixOf "00101001010100" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101001010100_3 : prefixOf "00101001010100" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101001010100_5 : prefixOf "00101001010100" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101001010100_6 : prefixOf "00101001010100" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101001010100_7 : prefixOf "00101001010100" 7 = "0010100" := by
  decide

@[simp] theorem prefix14_00101001010100_8 : prefixOf "00101001010100" 8 = "00101001" := by
  decide

@[simp] theorem prefix14_00101001010100_9 : prefixOf "00101001010100" 9 = "001010010" := by
  decide

@[simp] theorem prefix14_00101001010100_10 : prefixOf "00101001010100" 10 = "0010100101" := by
  decide

@[simp] theorem prefix14_00101001010100_11 : prefixOf "00101001010100" 11 = "00101001010" := by
  decide

@[simp] theorem prefix14_00101001010100_12 : prefixOf "00101001010100" 12 = "001010010101" := by
  decide

@[simp] theorem prefix14_00101001010100_13 : prefixOf "00101001010100" 13 = "0010100101010" := by
  decide

@[simp] theorem prefix14_00101001010100_14 : prefixOf "00101001010100" 14 = "00101001010100" := by
  decide

@[simp] theorem suffix14_00101001010100_7 : suffixFrom "00101001010100" 7 = "1010100" := by
  decide

@[simp] theorem suffix14_00101001010100_8 : suffixFrom "00101001010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_00101001010100_9 : suffixFrom "00101001010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_00101001010100_10 : suffixFrom "00101001010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_00101001010100_11 : suffixFrom "00101001010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_00101001010100_12 : suffixFrom "00101001010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_00101001010101_1 : prefixOf "00101001010101" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101001010101_2 : prefixOf "00101001010101" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101001010101_3 : prefixOf "00101001010101" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101001010101_5 : prefixOf "00101001010101" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101001010101_6 : prefixOf "00101001010101" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101001010101_7 : prefixOf "00101001010101" 7 = "0010100" := by
  decide

@[simp] theorem prefix14_00101001010101_8 : prefixOf "00101001010101" 8 = "00101001" := by
  decide

@[simp] theorem prefix14_00101001010101_9 : prefixOf "00101001010101" 9 = "001010010" := by
  decide

@[simp] theorem prefix14_00101001010101_10 : prefixOf "00101001010101" 10 = "0010100101" := by
  decide

@[simp] theorem prefix14_00101001010101_11 : prefixOf "00101001010101" 11 = "00101001010" := by
  decide

@[simp] theorem prefix14_00101001010101_12 : prefixOf "00101001010101" 12 = "001010010101" := by
  decide

@[simp] theorem prefix14_00101001010101_13 : prefixOf "00101001010101" 13 = "0010100101010" := by
  decide

@[simp] theorem prefix14_00101001010101_14 : prefixOf "00101001010101" 14 = "00101001010101" := by
  decide

@[simp] theorem suffix14_00101001010101_7 : suffixFrom "00101001010101" 7 = "1010101" := by
  decide

@[simp] theorem suffix14_00101001010101_8 : suffixFrom "00101001010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_00101001010101_9 : suffixFrom "00101001010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_00101001010101_10 : suffixFrom "00101001010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_00101001010101_11 : suffixFrom "00101001010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_00101001010101_12 : suffixFrom "00101001010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_00101010010010_1 : prefixOf "00101010010010" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101010010010_2 : prefixOf "00101010010010" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101010010010_3 : prefixOf "00101010010010" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101010010010_5 : prefixOf "00101010010010" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101010010010_6 : prefixOf "00101010010010" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101010010010_7 : prefixOf "00101010010010" 7 = "0010101" := by
  decide

@[simp] theorem prefix14_00101010010010_8 : prefixOf "00101010010010" 8 = "00101010" := by
  decide

@[simp] theorem prefix14_00101010010010_9 : prefixOf "00101010010010" 9 = "001010100" := by
  decide

@[simp] theorem prefix14_00101010010010_10 : prefixOf "00101010010010" 10 = "0010101001" := by
  decide

@[simp] theorem prefix14_00101010010010_11 : prefixOf "00101010010010" 11 = "00101010010" := by
  decide

@[simp] theorem prefix14_00101010010010_12 : prefixOf "00101010010010" 12 = "001010100100" := by
  decide

@[simp] theorem prefix14_00101010010010_13 : prefixOf "00101010010010" 13 = "0010101001001" := by
  decide

@[simp] theorem prefix14_00101010010010_14 : prefixOf "00101010010010" 14 = "00101010010010" := by
  decide

@[simp] theorem suffix14_00101010010010_7 : suffixFrom "00101010010010" 7 = "0010010" := by
  decide

@[simp] theorem suffix14_00101010010010_8 : suffixFrom "00101010010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_00101010010010_9 : suffixFrom "00101010010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_00101010010010_10 : suffixFrom "00101010010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_00101010010010_11 : suffixFrom "00101010010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_00101010010010_12 : suffixFrom "00101010010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_00101010010100_1 : prefixOf "00101010010100" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101010010100_2 : prefixOf "00101010010100" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101010010100_3 : prefixOf "00101010010100" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101010010100_5 : prefixOf "00101010010100" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101010010100_6 : prefixOf "00101010010100" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101010010100_7 : prefixOf "00101010010100" 7 = "0010101" := by
  decide

@[simp] theorem prefix14_00101010010100_8 : prefixOf "00101010010100" 8 = "00101010" := by
  decide

@[simp] theorem prefix14_00101010010100_9 : prefixOf "00101010010100" 9 = "001010100" := by
  decide

@[simp] theorem prefix14_00101010010100_10 : prefixOf "00101010010100" 10 = "0010101001" := by
  decide

@[simp] theorem prefix14_00101010010100_11 : prefixOf "00101010010100" 11 = "00101010010" := by
  decide

@[simp] theorem prefix14_00101010010100_12 : prefixOf "00101010010100" 12 = "001010100101" := by
  decide

@[simp] theorem prefix14_00101010010100_13 : prefixOf "00101010010100" 13 = "0010101001010" := by
  decide

@[simp] theorem prefix14_00101010010100_14 : prefixOf "00101010010100" 14 = "00101010010100" := by
  decide

@[simp] theorem suffix14_00101010010100_7 : suffixFrom "00101010010100" 7 = "0010100" := by
  decide

@[simp] theorem suffix14_00101010010100_8 : suffixFrom "00101010010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_00101010010100_9 : suffixFrom "00101010010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_00101010010100_10 : suffixFrom "00101010010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_00101010010100_11 : suffixFrom "00101010010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_00101010010100_12 : suffixFrom "00101010010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_00101010010101_1 : prefixOf "00101010010101" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101010010101_2 : prefixOf "00101010010101" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101010010101_3 : prefixOf "00101010010101" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101010010101_5 : prefixOf "00101010010101" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101010010101_6 : prefixOf "00101010010101" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101010010101_7 : prefixOf "00101010010101" 7 = "0010101" := by
  decide

@[simp] theorem prefix14_00101010010101_8 : prefixOf "00101010010101" 8 = "00101010" := by
  decide

@[simp] theorem prefix14_00101010010101_9 : prefixOf "00101010010101" 9 = "001010100" := by
  decide

@[simp] theorem prefix14_00101010010101_10 : prefixOf "00101010010101" 10 = "0010101001" := by
  decide

@[simp] theorem prefix14_00101010010101_11 : prefixOf "00101010010101" 11 = "00101010010" := by
  decide

@[simp] theorem prefix14_00101010010101_12 : prefixOf "00101010010101" 12 = "001010100101" := by
  decide

@[simp] theorem prefix14_00101010010101_13 : prefixOf "00101010010101" 13 = "0010101001010" := by
  decide

@[simp] theorem prefix14_00101010010101_14 : prefixOf "00101010010101" 14 = "00101010010101" := by
  decide

@[simp] theorem suffix14_00101010010101_7 : suffixFrom "00101010010101" 7 = "0010101" := by
  decide

@[simp] theorem suffix14_00101010010101_8 : suffixFrom "00101010010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_00101010010101_9 : suffixFrom "00101010010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_00101010010101_10 : suffixFrom "00101010010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_00101010010101_11 : suffixFrom "00101010010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_00101010010101_12 : suffixFrom "00101010010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_00101010100100_1 : prefixOf "00101010100100" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101010100100_2 : prefixOf "00101010100100" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101010100100_3 : prefixOf "00101010100100" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101010100100_5 : prefixOf "00101010100100" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101010100100_6 : prefixOf "00101010100100" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101010100100_7 : prefixOf "00101010100100" 7 = "0010101" := by
  decide

@[simp] theorem prefix14_00101010100100_8 : prefixOf "00101010100100" 8 = "00101010" := by
  decide

@[simp] theorem prefix14_00101010100100_9 : prefixOf "00101010100100" 9 = "001010101" := by
  decide

@[simp] theorem prefix14_00101010100100_10 : prefixOf "00101010100100" 10 = "0010101010" := by
  decide

@[simp] theorem prefix14_00101010100100_11 : prefixOf "00101010100100" 11 = "00101010100" := by
  decide

@[simp] theorem prefix14_00101010100100_12 : prefixOf "00101010100100" 12 = "001010101001" := by
  decide

@[simp] theorem prefix14_00101010100100_13 : prefixOf "00101010100100" 13 = "0010101010010" := by
  decide

@[simp] theorem prefix14_00101010100100_14 : prefixOf "00101010100100" 14 = "00101010100100" := by
  decide

@[simp] theorem suffix14_00101010100100_7 : suffixFrom "00101010100100" 7 = "0100100" := by
  decide

@[simp] theorem suffix14_00101010100100_8 : suffixFrom "00101010100100" 8 = "100100" := by
  decide

@[simp] theorem suffix14_00101010100100_9 : suffixFrom "00101010100100" 9 = "00100" := by
  decide

@[simp] theorem suffix14_00101010100100_10 : suffixFrom "00101010100100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_00101010100100_11 : suffixFrom "00101010100100" 11 = "100" := by
  decide

@[simp] theorem suffix14_00101010100100_12 : suffixFrom "00101010100100" 12 = "00" := by
  decide

@[simp] theorem prefix14_00101010100101_1 : prefixOf "00101010100101" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101010100101_2 : prefixOf "00101010100101" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101010100101_3 : prefixOf "00101010100101" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101010100101_5 : prefixOf "00101010100101" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101010100101_6 : prefixOf "00101010100101" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101010100101_7 : prefixOf "00101010100101" 7 = "0010101" := by
  decide

@[simp] theorem prefix14_00101010100101_8 : prefixOf "00101010100101" 8 = "00101010" := by
  decide

@[simp] theorem prefix14_00101010100101_9 : prefixOf "00101010100101" 9 = "001010101" := by
  decide

@[simp] theorem prefix14_00101010100101_10 : prefixOf "00101010100101" 10 = "0010101010" := by
  decide

@[simp] theorem prefix14_00101010100101_11 : prefixOf "00101010100101" 11 = "00101010100" := by
  decide

@[simp] theorem prefix14_00101010100101_12 : prefixOf "00101010100101" 12 = "001010101001" := by
  decide

@[simp] theorem prefix14_00101010100101_13 : prefixOf "00101010100101" 13 = "0010101010010" := by
  decide

@[simp] theorem prefix14_00101010100101_14 : prefixOf "00101010100101" 14 = "00101010100101" := by
  decide

@[simp] theorem suffix14_00101010100101_7 : suffixFrom "00101010100101" 7 = "0100101" := by
  decide

@[simp] theorem suffix14_00101010100101_8 : suffixFrom "00101010100101" 8 = "100101" := by
  decide

@[simp] theorem suffix14_00101010100101_9 : suffixFrom "00101010100101" 9 = "00101" := by
  decide

@[simp] theorem suffix14_00101010100101_10 : suffixFrom "00101010100101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_00101010100101_11 : suffixFrom "00101010100101" 11 = "101" := by
  decide

@[simp] theorem suffix14_00101010100101_12 : suffixFrom "00101010100101" 12 = "01" := by
  decide

@[simp] theorem prefix14_00101010101001_1 : prefixOf "00101010101001" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101010101001_2 : prefixOf "00101010101001" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101010101001_3 : prefixOf "00101010101001" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101010101001_5 : prefixOf "00101010101001" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101010101001_6 : prefixOf "00101010101001" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101010101001_7 : prefixOf "00101010101001" 7 = "0010101" := by
  decide

@[simp] theorem prefix14_00101010101001_8 : prefixOf "00101010101001" 8 = "00101010" := by
  decide

@[simp] theorem prefix14_00101010101001_9 : prefixOf "00101010101001" 9 = "001010101" := by
  decide

@[simp] theorem prefix14_00101010101001_10 : prefixOf "00101010101001" 10 = "0010101010" := by
  decide

@[simp] theorem prefix14_00101010101001_11 : prefixOf "00101010101001" 11 = "00101010101" := by
  decide

@[simp] theorem prefix14_00101010101001_12 : prefixOf "00101010101001" 12 = "001010101010" := by
  decide

@[simp] theorem prefix14_00101010101001_13 : prefixOf "00101010101001" 13 = "0010101010100" := by
  decide

@[simp] theorem prefix14_00101010101001_14 : prefixOf "00101010101001" 14 = "00101010101001" := by
  decide

@[simp] theorem suffix14_00101010101001_7 : suffixFrom "00101010101001" 7 = "0101001" := by
  decide

@[simp] theorem suffix14_00101010101001_8 : suffixFrom "00101010101001" 8 = "101001" := by
  decide

@[simp] theorem suffix14_00101010101001_9 : suffixFrom "00101010101001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_00101010101001_10 : suffixFrom "00101010101001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_00101010101001_11 : suffixFrom "00101010101001" 11 = "001" := by
  decide

@[simp] theorem suffix14_00101010101001_12 : suffixFrom "00101010101001" 12 = "01" := by
  decide

@[simp] theorem prefix14_00101010101010_1 : prefixOf "00101010101010" 1 = "0" := by
  decide

@[simp] theorem prefix14_00101010101010_2 : prefixOf "00101010101010" 2 = "00" := by
  decide

@[simp] theorem prefix14_00101010101010_3 : prefixOf "00101010101010" 3 = "001" := by
  decide

@[simp] theorem prefix14_00101010101010_5 : prefixOf "00101010101010" 5 = "00101" := by
  decide

@[simp] theorem prefix14_00101010101010_6 : prefixOf "00101010101010" 6 = "001010" := by
  decide

@[simp] theorem prefix14_00101010101010_7 : prefixOf "00101010101010" 7 = "0010101" := by
  decide

@[simp] theorem prefix14_00101010101010_8 : prefixOf "00101010101010" 8 = "00101010" := by
  decide

@[simp] theorem prefix14_00101010101010_9 : prefixOf "00101010101010" 9 = "001010101" := by
  decide

@[simp] theorem prefix14_00101010101010_10 : prefixOf "00101010101010" 10 = "0010101010" := by
  decide

@[simp] theorem prefix14_00101010101010_11 : prefixOf "00101010101010" 11 = "00101010101" := by
  decide

@[simp] theorem prefix14_00101010101010_12 : prefixOf "00101010101010" 12 = "001010101010" := by
  decide

@[simp] theorem prefix14_00101010101010_13 : prefixOf "00101010101010" 13 = "0010101010101" := by
  decide

@[simp] theorem prefix14_00101010101010_14 : prefixOf "00101010101010" 14 = "00101010101010" := by
  decide

@[simp] theorem suffix14_00101010101010_7 : suffixFrom "00101010101010" 7 = "0101010" := by
  decide

@[simp] theorem suffix14_00101010101010_8 : suffixFrom "00101010101010" 8 = "101010" := by
  decide

@[simp] theorem suffix14_00101010101010_9 : suffixFrom "00101010101010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_00101010101010_10 : suffixFrom "00101010101010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_00101010101010_11 : suffixFrom "00101010101010" 11 = "010" := by
  decide

@[simp] theorem suffix14_00101010101010_12 : suffixFrom "00101010101010" 12 = "10" := by
  decide

@[simp] theorem prefix14_01001001001001_1 : prefixOf "01001001001001" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001001001001_2 : prefixOf "01001001001001" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001001001001_3 : prefixOf "01001001001001" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001001001001_5 : prefixOf "01001001001001" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001001001001_6 : prefixOf "01001001001001" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001001001001_7 : prefixOf "01001001001001" 7 = "0100100" := by
  decide

@[simp] theorem prefix14_01001001001001_8 : prefixOf "01001001001001" 8 = "01001001" := by
  decide

@[simp] theorem prefix14_01001001001001_9 : prefixOf "01001001001001" 9 = "010010010" := by
  decide

@[simp] theorem prefix14_01001001001001_10 : prefixOf "01001001001001" 10 = "0100100100" := by
  decide

@[simp] theorem prefix14_01001001001001_11 : prefixOf "01001001001001" 11 = "01001001001" := by
  decide

@[simp] theorem prefix14_01001001001001_12 : prefixOf "01001001001001" 12 = "010010010010" := by
  decide

@[simp] theorem prefix14_01001001001001_13 : prefixOf "01001001001001" 13 = "0100100100100" := by
  decide

@[simp] theorem prefix14_01001001001001_14 : prefixOf "01001001001001" 14 = "01001001001001" := by
  decide

@[simp] theorem suffix14_01001001001001_7 : suffixFrom "01001001001001" 7 = "1001001" := by
  decide

@[simp] theorem suffix14_01001001001001_8 : suffixFrom "01001001001001" 8 = "001001" := by
  decide

@[simp] theorem suffix14_01001001001001_9 : suffixFrom "01001001001001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_01001001001001_10 : suffixFrom "01001001001001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_01001001001001_11 : suffixFrom "01001001001001" 11 = "001" := by
  decide

@[simp] theorem suffix14_01001001001001_12 : suffixFrom "01001001001001" 12 = "01" := by
  decide

@[simp] theorem prefix14_01001001001010_1 : prefixOf "01001001001010" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001001001010_2 : prefixOf "01001001001010" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001001001010_3 : prefixOf "01001001001010" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001001001010_5 : prefixOf "01001001001010" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001001001010_6 : prefixOf "01001001001010" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001001001010_7 : prefixOf "01001001001010" 7 = "0100100" := by
  decide

@[simp] theorem prefix14_01001001001010_8 : prefixOf "01001001001010" 8 = "01001001" := by
  decide

@[simp] theorem prefix14_01001001001010_9 : prefixOf "01001001001010" 9 = "010010010" := by
  decide

@[simp] theorem prefix14_01001001001010_10 : prefixOf "01001001001010" 10 = "0100100100" := by
  decide

@[simp] theorem prefix14_01001001001010_11 : prefixOf "01001001001010" 11 = "01001001001" := by
  decide

@[simp] theorem prefix14_01001001001010_12 : prefixOf "01001001001010" 12 = "010010010010" := by
  decide

@[simp] theorem prefix14_01001001001010_13 : prefixOf "01001001001010" 13 = "0100100100101" := by
  decide

@[simp] theorem prefix14_01001001001010_14 : prefixOf "01001001001010" 14 = "01001001001010" := by
  decide

@[simp] theorem suffix14_01001001001010_7 : suffixFrom "01001001001010" 7 = "1001010" := by
  decide

@[simp] theorem suffix14_01001001001010_8 : suffixFrom "01001001001010" 8 = "001010" := by
  decide

@[simp] theorem suffix14_01001001001010_9 : suffixFrom "01001001001010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_01001001001010_10 : suffixFrom "01001001001010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_01001001001010_11 : suffixFrom "01001001001010" 11 = "010" := by
  decide

@[simp] theorem suffix14_01001001001010_12 : suffixFrom "01001001001010" 12 = "10" := by
  decide

@[simp] theorem prefix14_01001001010010_1 : prefixOf "01001001010010" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001001010010_2 : prefixOf "01001001010010" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001001010010_3 : prefixOf "01001001010010" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001001010010_5 : prefixOf "01001001010010" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001001010010_6 : prefixOf "01001001010010" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001001010010_7 : prefixOf "01001001010010" 7 = "0100100" := by
  decide

@[simp] theorem prefix14_01001001010010_8 : prefixOf "01001001010010" 8 = "01001001" := by
  decide

@[simp] theorem prefix14_01001001010010_9 : prefixOf "01001001010010" 9 = "010010010" := by
  decide

@[simp] theorem prefix14_01001001010010_10 : prefixOf "01001001010010" 10 = "0100100101" := by
  decide

@[simp] theorem prefix14_01001001010010_11 : prefixOf "01001001010010" 11 = "01001001010" := by
  decide

@[simp] theorem prefix14_01001001010010_12 : prefixOf "01001001010010" 12 = "010010010100" := by
  decide

@[simp] theorem prefix14_01001001010010_13 : prefixOf "01001001010010" 13 = "0100100101001" := by
  decide

@[simp] theorem prefix14_01001001010010_14 : prefixOf "01001001010010" 14 = "01001001010010" := by
  decide

@[simp] theorem suffix14_01001001010010_7 : suffixFrom "01001001010010" 7 = "1010010" := by
  decide

@[simp] theorem suffix14_01001001010010_8 : suffixFrom "01001001010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_01001001010010_9 : suffixFrom "01001001010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_01001001010010_10 : suffixFrom "01001001010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_01001001010010_11 : suffixFrom "01001001010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_01001001010010_12 : suffixFrom "01001001010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_01001001010100_1 : prefixOf "01001001010100" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001001010100_2 : prefixOf "01001001010100" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001001010100_3 : prefixOf "01001001010100" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001001010100_5 : prefixOf "01001001010100" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001001010100_6 : prefixOf "01001001010100" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001001010100_7 : prefixOf "01001001010100" 7 = "0100100" := by
  decide

@[simp] theorem prefix14_01001001010100_8 : prefixOf "01001001010100" 8 = "01001001" := by
  decide

@[simp] theorem prefix14_01001001010100_9 : prefixOf "01001001010100" 9 = "010010010" := by
  decide

@[simp] theorem prefix14_01001001010100_10 : prefixOf "01001001010100" 10 = "0100100101" := by
  decide

@[simp] theorem prefix14_01001001010100_11 : prefixOf "01001001010100" 11 = "01001001010" := by
  decide

@[simp] theorem prefix14_01001001010100_12 : prefixOf "01001001010100" 12 = "010010010101" := by
  decide

@[simp] theorem prefix14_01001001010100_13 : prefixOf "01001001010100" 13 = "0100100101010" := by
  decide

@[simp] theorem prefix14_01001001010100_14 : prefixOf "01001001010100" 14 = "01001001010100" := by
  decide

@[simp] theorem suffix14_01001001010100_7 : suffixFrom "01001001010100" 7 = "1010100" := by
  decide

@[simp] theorem suffix14_01001001010100_8 : suffixFrom "01001001010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_01001001010100_9 : suffixFrom "01001001010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_01001001010100_10 : suffixFrom "01001001010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_01001001010100_11 : suffixFrom "01001001010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_01001001010100_12 : suffixFrom "01001001010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_01001001010101_1 : prefixOf "01001001010101" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001001010101_2 : prefixOf "01001001010101" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001001010101_3 : prefixOf "01001001010101" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001001010101_5 : prefixOf "01001001010101" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001001010101_6 : prefixOf "01001001010101" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001001010101_7 : prefixOf "01001001010101" 7 = "0100100" := by
  decide

@[simp] theorem prefix14_01001001010101_8 : prefixOf "01001001010101" 8 = "01001001" := by
  decide

@[simp] theorem prefix14_01001001010101_9 : prefixOf "01001001010101" 9 = "010010010" := by
  decide

@[simp] theorem prefix14_01001001010101_10 : prefixOf "01001001010101" 10 = "0100100101" := by
  decide

@[simp] theorem prefix14_01001001010101_11 : prefixOf "01001001010101" 11 = "01001001010" := by
  decide

@[simp] theorem prefix14_01001001010101_12 : prefixOf "01001001010101" 12 = "010010010101" := by
  decide

@[simp] theorem prefix14_01001001010101_13 : prefixOf "01001001010101" 13 = "0100100101010" := by
  decide

@[simp] theorem prefix14_01001001010101_14 : prefixOf "01001001010101" 14 = "01001001010101" := by
  decide

@[simp] theorem suffix14_01001001010101_7 : suffixFrom "01001001010101" 7 = "1010101" := by
  decide

@[simp] theorem suffix14_01001001010101_8 : suffixFrom "01001001010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_01001001010101_9 : suffixFrom "01001001010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_01001001010101_10 : suffixFrom "01001001010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_01001001010101_11 : suffixFrom "01001001010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_01001001010101_12 : suffixFrom "01001001010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_01001010010010_1 : prefixOf "01001010010010" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001010010010_2 : prefixOf "01001010010010" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001010010010_3 : prefixOf "01001010010010" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001010010010_5 : prefixOf "01001010010010" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001010010010_6 : prefixOf "01001010010010" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001010010010_7 : prefixOf "01001010010010" 7 = "0100101" := by
  decide

@[simp] theorem prefix14_01001010010010_8 : prefixOf "01001010010010" 8 = "01001010" := by
  decide

@[simp] theorem prefix14_01001010010010_9 : prefixOf "01001010010010" 9 = "010010100" := by
  decide

@[simp] theorem prefix14_01001010010010_10 : prefixOf "01001010010010" 10 = "0100101001" := by
  decide

@[simp] theorem prefix14_01001010010010_11 : prefixOf "01001010010010" 11 = "01001010010" := by
  decide

@[simp] theorem prefix14_01001010010010_12 : prefixOf "01001010010010" 12 = "010010100100" := by
  decide

@[simp] theorem prefix14_01001010010010_13 : prefixOf "01001010010010" 13 = "0100101001001" := by
  decide

@[simp] theorem prefix14_01001010010010_14 : prefixOf "01001010010010" 14 = "01001010010010" := by
  decide

@[simp] theorem suffix14_01001010010010_7 : suffixFrom "01001010010010" 7 = "0010010" := by
  decide

@[simp] theorem suffix14_01001010010010_8 : suffixFrom "01001010010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_01001010010010_9 : suffixFrom "01001010010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_01001010010010_10 : suffixFrom "01001010010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_01001010010010_11 : suffixFrom "01001010010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_01001010010010_12 : suffixFrom "01001010010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_01001010010100_1 : prefixOf "01001010010100" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001010010100_2 : prefixOf "01001010010100" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001010010100_3 : prefixOf "01001010010100" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001010010100_5 : prefixOf "01001010010100" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001010010100_6 : prefixOf "01001010010100" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001010010100_7 : prefixOf "01001010010100" 7 = "0100101" := by
  decide

@[simp] theorem prefix14_01001010010100_8 : prefixOf "01001010010100" 8 = "01001010" := by
  decide

@[simp] theorem prefix14_01001010010100_9 : prefixOf "01001010010100" 9 = "010010100" := by
  decide

@[simp] theorem prefix14_01001010010100_10 : prefixOf "01001010010100" 10 = "0100101001" := by
  decide

@[simp] theorem prefix14_01001010010100_11 : prefixOf "01001010010100" 11 = "01001010010" := by
  decide

@[simp] theorem prefix14_01001010010100_12 : prefixOf "01001010010100" 12 = "010010100101" := by
  decide

@[simp] theorem prefix14_01001010010100_13 : prefixOf "01001010010100" 13 = "0100101001010" := by
  decide

@[simp] theorem prefix14_01001010010100_14 : prefixOf "01001010010100" 14 = "01001010010100" := by
  decide

@[simp] theorem suffix14_01001010010100_7 : suffixFrom "01001010010100" 7 = "0010100" := by
  decide

@[simp] theorem suffix14_01001010010100_8 : suffixFrom "01001010010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_01001010010100_9 : suffixFrom "01001010010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_01001010010100_10 : suffixFrom "01001010010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_01001010010100_11 : suffixFrom "01001010010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_01001010010100_12 : suffixFrom "01001010010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_01001010010101_1 : prefixOf "01001010010101" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001010010101_2 : prefixOf "01001010010101" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001010010101_3 : prefixOf "01001010010101" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001010010101_5 : prefixOf "01001010010101" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001010010101_6 : prefixOf "01001010010101" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001010010101_7 : prefixOf "01001010010101" 7 = "0100101" := by
  decide

@[simp] theorem prefix14_01001010010101_8 : prefixOf "01001010010101" 8 = "01001010" := by
  decide

@[simp] theorem prefix14_01001010010101_9 : prefixOf "01001010010101" 9 = "010010100" := by
  decide

@[simp] theorem prefix14_01001010010101_10 : prefixOf "01001010010101" 10 = "0100101001" := by
  decide

@[simp] theorem prefix14_01001010010101_11 : prefixOf "01001010010101" 11 = "01001010010" := by
  decide

@[simp] theorem prefix14_01001010010101_12 : prefixOf "01001010010101" 12 = "010010100101" := by
  decide

@[simp] theorem prefix14_01001010010101_13 : prefixOf "01001010010101" 13 = "0100101001010" := by
  decide

@[simp] theorem prefix14_01001010010101_14 : prefixOf "01001010010101" 14 = "01001010010101" := by
  decide

@[simp] theorem suffix14_01001010010101_7 : suffixFrom "01001010010101" 7 = "0010101" := by
  decide

@[simp] theorem suffix14_01001010010101_8 : suffixFrom "01001010010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_01001010010101_9 : suffixFrom "01001010010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_01001010010101_10 : suffixFrom "01001010010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_01001010010101_11 : suffixFrom "01001010010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_01001010010101_12 : suffixFrom "01001010010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_01001010100100_1 : prefixOf "01001010100100" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001010100100_2 : prefixOf "01001010100100" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001010100100_3 : prefixOf "01001010100100" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001010100100_5 : prefixOf "01001010100100" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001010100100_6 : prefixOf "01001010100100" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001010100100_7 : prefixOf "01001010100100" 7 = "0100101" := by
  decide

@[simp] theorem prefix14_01001010100100_8 : prefixOf "01001010100100" 8 = "01001010" := by
  decide

@[simp] theorem prefix14_01001010100100_9 : prefixOf "01001010100100" 9 = "010010101" := by
  decide

@[simp] theorem prefix14_01001010100100_10 : prefixOf "01001010100100" 10 = "0100101010" := by
  decide

@[simp] theorem prefix14_01001010100100_11 : prefixOf "01001010100100" 11 = "01001010100" := by
  decide

@[simp] theorem prefix14_01001010100100_12 : prefixOf "01001010100100" 12 = "010010101001" := by
  decide

@[simp] theorem prefix14_01001010100100_13 : prefixOf "01001010100100" 13 = "0100101010010" := by
  decide

@[simp] theorem prefix14_01001010100100_14 : prefixOf "01001010100100" 14 = "01001010100100" := by
  decide

@[simp] theorem suffix14_01001010100100_7 : suffixFrom "01001010100100" 7 = "0100100" := by
  decide

@[simp] theorem suffix14_01001010100100_8 : suffixFrom "01001010100100" 8 = "100100" := by
  decide

@[simp] theorem suffix14_01001010100100_9 : suffixFrom "01001010100100" 9 = "00100" := by
  decide

@[simp] theorem suffix14_01001010100100_10 : suffixFrom "01001010100100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_01001010100100_11 : suffixFrom "01001010100100" 11 = "100" := by
  decide

@[simp] theorem suffix14_01001010100100_12 : suffixFrom "01001010100100" 12 = "00" := by
  decide

@[simp] theorem prefix14_01001010100101_1 : prefixOf "01001010100101" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001010100101_2 : prefixOf "01001010100101" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001010100101_3 : prefixOf "01001010100101" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001010100101_5 : prefixOf "01001010100101" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001010100101_6 : prefixOf "01001010100101" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001010100101_7 : prefixOf "01001010100101" 7 = "0100101" := by
  decide

@[simp] theorem prefix14_01001010100101_8 : prefixOf "01001010100101" 8 = "01001010" := by
  decide

@[simp] theorem prefix14_01001010100101_9 : prefixOf "01001010100101" 9 = "010010101" := by
  decide

@[simp] theorem prefix14_01001010100101_10 : prefixOf "01001010100101" 10 = "0100101010" := by
  decide

@[simp] theorem prefix14_01001010100101_11 : prefixOf "01001010100101" 11 = "01001010100" := by
  decide

@[simp] theorem prefix14_01001010100101_12 : prefixOf "01001010100101" 12 = "010010101001" := by
  decide

@[simp] theorem prefix14_01001010100101_13 : prefixOf "01001010100101" 13 = "0100101010010" := by
  decide

@[simp] theorem prefix14_01001010100101_14 : prefixOf "01001010100101" 14 = "01001010100101" := by
  decide

@[simp] theorem suffix14_01001010100101_7 : suffixFrom "01001010100101" 7 = "0100101" := by
  decide

@[simp] theorem suffix14_01001010100101_8 : suffixFrom "01001010100101" 8 = "100101" := by
  decide

@[simp] theorem suffix14_01001010100101_9 : suffixFrom "01001010100101" 9 = "00101" := by
  decide

@[simp] theorem suffix14_01001010100101_10 : suffixFrom "01001010100101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_01001010100101_11 : suffixFrom "01001010100101" 11 = "101" := by
  decide

@[simp] theorem suffix14_01001010100101_12 : suffixFrom "01001010100101" 12 = "01" := by
  decide

@[simp] theorem prefix14_01001010101001_1 : prefixOf "01001010101001" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001010101001_2 : prefixOf "01001010101001" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001010101001_3 : prefixOf "01001010101001" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001010101001_5 : prefixOf "01001010101001" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001010101001_6 : prefixOf "01001010101001" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001010101001_7 : prefixOf "01001010101001" 7 = "0100101" := by
  decide

@[simp] theorem prefix14_01001010101001_8 : prefixOf "01001010101001" 8 = "01001010" := by
  decide

@[simp] theorem prefix14_01001010101001_9 : prefixOf "01001010101001" 9 = "010010101" := by
  decide

@[simp] theorem prefix14_01001010101001_10 : prefixOf "01001010101001" 10 = "0100101010" := by
  decide

@[simp] theorem prefix14_01001010101001_11 : prefixOf "01001010101001" 11 = "01001010101" := by
  decide

@[simp] theorem prefix14_01001010101001_12 : prefixOf "01001010101001" 12 = "010010101010" := by
  decide

@[simp] theorem prefix14_01001010101001_13 : prefixOf "01001010101001" 13 = "0100101010100" := by
  decide

@[simp] theorem prefix14_01001010101001_14 : prefixOf "01001010101001" 14 = "01001010101001" := by
  decide

@[simp] theorem suffix14_01001010101001_7 : suffixFrom "01001010101001" 7 = "0101001" := by
  decide

@[simp] theorem suffix14_01001010101001_8 : suffixFrom "01001010101001" 8 = "101001" := by
  decide

@[simp] theorem suffix14_01001010101001_9 : suffixFrom "01001010101001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_01001010101001_10 : suffixFrom "01001010101001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_01001010101001_11 : suffixFrom "01001010101001" 11 = "001" := by
  decide

@[simp] theorem suffix14_01001010101001_12 : suffixFrom "01001010101001" 12 = "01" := by
  decide

@[simp] theorem prefix14_01001010101010_1 : prefixOf "01001010101010" 1 = "0" := by
  decide

@[simp] theorem prefix14_01001010101010_2 : prefixOf "01001010101010" 2 = "01" := by
  decide

@[simp] theorem prefix14_01001010101010_3 : prefixOf "01001010101010" 3 = "010" := by
  decide

@[simp] theorem prefix14_01001010101010_5 : prefixOf "01001010101010" 5 = "01001" := by
  decide

@[simp] theorem prefix14_01001010101010_6 : prefixOf "01001010101010" 6 = "010010" := by
  decide

@[simp] theorem prefix14_01001010101010_7 : prefixOf "01001010101010" 7 = "0100101" := by
  decide

@[simp] theorem prefix14_01001010101010_8 : prefixOf "01001010101010" 8 = "01001010" := by
  decide

@[simp] theorem prefix14_01001010101010_9 : prefixOf "01001010101010" 9 = "010010101" := by
  decide

@[simp] theorem prefix14_01001010101010_10 : prefixOf "01001010101010" 10 = "0100101010" := by
  decide

@[simp] theorem prefix14_01001010101010_11 : prefixOf "01001010101010" 11 = "01001010101" := by
  decide

@[simp] theorem prefix14_01001010101010_12 : prefixOf "01001010101010" 12 = "010010101010" := by
  decide

@[simp] theorem prefix14_01001010101010_13 : prefixOf "01001010101010" 13 = "0100101010101" := by
  decide

@[simp] theorem prefix14_01001010101010_14 : prefixOf "01001010101010" 14 = "01001010101010" := by
  decide

@[simp] theorem suffix14_01001010101010_7 : suffixFrom "01001010101010" 7 = "0101010" := by
  decide

@[simp] theorem suffix14_01001010101010_8 : suffixFrom "01001010101010" 8 = "101010" := by
  decide

@[simp] theorem suffix14_01001010101010_9 : suffixFrom "01001010101010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_01001010101010_10 : suffixFrom "01001010101010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_01001010101010_11 : suffixFrom "01001010101010" 11 = "010" := by
  decide

@[simp] theorem suffix14_01001010101010_12 : suffixFrom "01001010101010" 12 = "10" := by
  decide

@[simp] theorem prefix14_01010010010010_1 : prefixOf "01010010010010" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010010010010_2 : prefixOf "01010010010010" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010010010010_3 : prefixOf "01010010010010" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010010010010_5 : prefixOf "01010010010010" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010010010010_6 : prefixOf "01010010010010" 6 = "010100" := by
  decide

@[simp] theorem prefix14_01010010010010_7 : prefixOf "01010010010010" 7 = "0101001" := by
  decide

@[simp] theorem prefix14_01010010010010_8 : prefixOf "01010010010010" 8 = "01010010" := by
  decide

@[simp] theorem prefix14_01010010010010_9 : prefixOf "01010010010010" 9 = "010100100" := by
  decide

@[simp] theorem prefix14_01010010010010_10 : prefixOf "01010010010010" 10 = "0101001001" := by
  decide

@[simp] theorem prefix14_01010010010010_11 : prefixOf "01010010010010" 11 = "01010010010" := by
  decide

@[simp] theorem prefix14_01010010010010_12 : prefixOf "01010010010010" 12 = "010100100100" := by
  decide

@[simp] theorem prefix14_01010010010010_13 : prefixOf "01010010010010" 13 = "0101001001001" := by
  decide

@[simp] theorem prefix14_01010010010010_14 : prefixOf "01010010010010" 14 = "01010010010010" := by
  decide

@[simp] theorem suffix14_01010010010010_7 : suffixFrom "01010010010010" 7 = "0010010" := by
  decide

@[simp] theorem suffix14_01010010010010_8 : suffixFrom "01010010010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_01010010010010_9 : suffixFrom "01010010010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_01010010010010_10 : suffixFrom "01010010010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_01010010010010_11 : suffixFrom "01010010010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_01010010010010_12 : suffixFrom "01010010010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_01010010010100_1 : prefixOf "01010010010100" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010010010100_2 : prefixOf "01010010010100" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010010010100_3 : prefixOf "01010010010100" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010010010100_5 : prefixOf "01010010010100" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010010010100_6 : prefixOf "01010010010100" 6 = "010100" := by
  decide

@[simp] theorem prefix14_01010010010100_7 : prefixOf "01010010010100" 7 = "0101001" := by
  decide

@[simp] theorem prefix14_01010010010100_8 : prefixOf "01010010010100" 8 = "01010010" := by
  decide

@[simp] theorem prefix14_01010010010100_9 : prefixOf "01010010010100" 9 = "010100100" := by
  decide

@[simp] theorem prefix14_01010010010100_10 : prefixOf "01010010010100" 10 = "0101001001" := by
  decide

@[simp] theorem prefix14_01010010010100_11 : prefixOf "01010010010100" 11 = "01010010010" := by
  decide

@[simp] theorem prefix14_01010010010100_12 : prefixOf "01010010010100" 12 = "010100100101" := by
  decide

@[simp] theorem prefix14_01010010010100_13 : prefixOf "01010010010100" 13 = "0101001001010" := by
  decide

@[simp] theorem prefix14_01010010010100_14 : prefixOf "01010010010100" 14 = "01010010010100" := by
  decide

@[simp] theorem suffix14_01010010010100_7 : suffixFrom "01010010010100" 7 = "0010100" := by
  decide

@[simp] theorem suffix14_01010010010100_8 : suffixFrom "01010010010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_01010010010100_9 : suffixFrom "01010010010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_01010010010100_10 : suffixFrom "01010010010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_01010010010100_11 : suffixFrom "01010010010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_01010010010100_12 : suffixFrom "01010010010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_01010010010101_1 : prefixOf "01010010010101" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010010010101_2 : prefixOf "01010010010101" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010010010101_3 : prefixOf "01010010010101" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010010010101_5 : prefixOf "01010010010101" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010010010101_6 : prefixOf "01010010010101" 6 = "010100" := by
  decide

@[simp] theorem prefix14_01010010010101_7 : prefixOf "01010010010101" 7 = "0101001" := by
  decide

@[simp] theorem prefix14_01010010010101_8 : prefixOf "01010010010101" 8 = "01010010" := by
  decide

@[simp] theorem prefix14_01010010010101_9 : prefixOf "01010010010101" 9 = "010100100" := by
  decide

@[simp] theorem prefix14_01010010010101_10 : prefixOf "01010010010101" 10 = "0101001001" := by
  decide

@[simp] theorem prefix14_01010010010101_11 : prefixOf "01010010010101" 11 = "01010010010" := by
  decide

@[simp] theorem prefix14_01010010010101_12 : prefixOf "01010010010101" 12 = "010100100101" := by
  decide

@[simp] theorem prefix14_01010010010101_13 : prefixOf "01010010010101" 13 = "0101001001010" := by
  decide

@[simp] theorem prefix14_01010010010101_14 : prefixOf "01010010010101" 14 = "01010010010101" := by
  decide

@[simp] theorem suffix14_01010010010101_7 : suffixFrom "01010010010101" 7 = "0010101" := by
  decide

@[simp] theorem suffix14_01010010010101_8 : suffixFrom "01010010010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_01010010010101_9 : suffixFrom "01010010010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_01010010010101_10 : suffixFrom "01010010010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_01010010010101_11 : suffixFrom "01010010010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_01010010010101_12 : suffixFrom "01010010010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_01010010100100_1 : prefixOf "01010010100100" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010010100100_2 : prefixOf "01010010100100" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010010100100_3 : prefixOf "01010010100100" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010010100100_5 : prefixOf "01010010100100" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010010100100_6 : prefixOf "01010010100100" 6 = "010100" := by
  decide

@[simp] theorem prefix14_01010010100100_7 : prefixOf "01010010100100" 7 = "0101001" := by
  decide

@[simp] theorem prefix14_01010010100100_8 : prefixOf "01010010100100" 8 = "01010010" := by
  decide

@[simp] theorem prefix14_01010010100100_9 : prefixOf "01010010100100" 9 = "010100101" := by
  decide

@[simp] theorem prefix14_01010010100100_10 : prefixOf "01010010100100" 10 = "0101001010" := by
  decide

@[simp] theorem prefix14_01010010100100_11 : prefixOf "01010010100100" 11 = "01010010100" := by
  decide

@[simp] theorem prefix14_01010010100100_12 : prefixOf "01010010100100" 12 = "010100101001" := by
  decide

@[simp] theorem prefix14_01010010100100_13 : prefixOf "01010010100100" 13 = "0101001010010" := by
  decide

@[simp] theorem prefix14_01010010100100_14 : prefixOf "01010010100100" 14 = "01010010100100" := by
  decide

@[simp] theorem suffix14_01010010100100_7 : suffixFrom "01010010100100" 7 = "0100100" := by
  decide

@[simp] theorem suffix14_01010010100100_8 : suffixFrom "01010010100100" 8 = "100100" := by
  decide

@[simp] theorem suffix14_01010010100100_9 : suffixFrom "01010010100100" 9 = "00100" := by
  decide

@[simp] theorem suffix14_01010010100100_10 : suffixFrom "01010010100100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_01010010100100_11 : suffixFrom "01010010100100" 11 = "100" := by
  decide

@[simp] theorem suffix14_01010010100100_12 : suffixFrom "01010010100100" 12 = "00" := by
  decide

@[simp] theorem prefix14_01010010100101_1 : prefixOf "01010010100101" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010010100101_2 : prefixOf "01010010100101" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010010100101_3 : prefixOf "01010010100101" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010010100101_5 : prefixOf "01010010100101" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010010100101_6 : prefixOf "01010010100101" 6 = "010100" := by
  decide

@[simp] theorem prefix14_01010010100101_7 : prefixOf "01010010100101" 7 = "0101001" := by
  decide

@[simp] theorem prefix14_01010010100101_8 : prefixOf "01010010100101" 8 = "01010010" := by
  decide

@[simp] theorem prefix14_01010010100101_9 : prefixOf "01010010100101" 9 = "010100101" := by
  decide

@[simp] theorem prefix14_01010010100101_10 : prefixOf "01010010100101" 10 = "0101001010" := by
  decide

@[simp] theorem prefix14_01010010100101_11 : prefixOf "01010010100101" 11 = "01010010100" := by
  decide

@[simp] theorem prefix14_01010010100101_12 : prefixOf "01010010100101" 12 = "010100101001" := by
  decide

@[simp] theorem prefix14_01010010100101_13 : prefixOf "01010010100101" 13 = "0101001010010" := by
  decide

@[simp] theorem prefix14_01010010100101_14 : prefixOf "01010010100101" 14 = "01010010100101" := by
  decide

@[simp] theorem suffix14_01010010100101_7 : suffixFrom "01010010100101" 7 = "0100101" := by
  decide

@[simp] theorem suffix14_01010010100101_8 : suffixFrom "01010010100101" 8 = "100101" := by
  decide

@[simp] theorem suffix14_01010010100101_9 : suffixFrom "01010010100101" 9 = "00101" := by
  decide

@[simp] theorem suffix14_01010010100101_10 : suffixFrom "01010010100101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_01010010100101_11 : suffixFrom "01010010100101" 11 = "101" := by
  decide

@[simp] theorem suffix14_01010010100101_12 : suffixFrom "01010010100101" 12 = "01" := by
  decide

@[simp] theorem prefix14_01010010101001_1 : prefixOf "01010010101001" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010010101001_2 : prefixOf "01010010101001" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010010101001_3 : prefixOf "01010010101001" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010010101001_5 : prefixOf "01010010101001" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010010101001_6 : prefixOf "01010010101001" 6 = "010100" := by
  decide

@[simp] theorem prefix14_01010010101001_7 : prefixOf "01010010101001" 7 = "0101001" := by
  decide

@[simp] theorem prefix14_01010010101001_8 : prefixOf "01010010101001" 8 = "01010010" := by
  decide

@[simp] theorem prefix14_01010010101001_9 : prefixOf "01010010101001" 9 = "010100101" := by
  decide

@[simp] theorem prefix14_01010010101001_10 : prefixOf "01010010101001" 10 = "0101001010" := by
  decide

@[simp] theorem prefix14_01010010101001_11 : prefixOf "01010010101001" 11 = "01010010101" := by
  decide

@[simp] theorem prefix14_01010010101001_12 : prefixOf "01010010101001" 12 = "010100101010" := by
  decide

@[simp] theorem prefix14_01010010101001_13 : prefixOf "01010010101001" 13 = "0101001010100" := by
  decide

@[simp] theorem prefix14_01010010101001_14 : prefixOf "01010010101001" 14 = "01010010101001" := by
  decide

@[simp] theorem suffix14_01010010101001_7 : suffixFrom "01010010101001" 7 = "0101001" := by
  decide

@[simp] theorem suffix14_01010010101001_8 : suffixFrom "01010010101001" 8 = "101001" := by
  decide

@[simp] theorem suffix14_01010010101001_9 : suffixFrom "01010010101001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_01010010101001_10 : suffixFrom "01010010101001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_01010010101001_11 : suffixFrom "01010010101001" 11 = "001" := by
  decide

@[simp] theorem suffix14_01010010101001_12 : suffixFrom "01010010101001" 12 = "01" := by
  decide

@[simp] theorem prefix14_01010010101010_1 : prefixOf "01010010101010" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010010101010_2 : prefixOf "01010010101010" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010010101010_3 : prefixOf "01010010101010" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010010101010_5 : prefixOf "01010010101010" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010010101010_6 : prefixOf "01010010101010" 6 = "010100" := by
  decide

@[simp] theorem prefix14_01010010101010_7 : prefixOf "01010010101010" 7 = "0101001" := by
  decide

@[simp] theorem prefix14_01010010101010_8 : prefixOf "01010010101010" 8 = "01010010" := by
  decide

@[simp] theorem prefix14_01010010101010_9 : prefixOf "01010010101010" 9 = "010100101" := by
  decide

@[simp] theorem prefix14_01010010101010_10 : prefixOf "01010010101010" 10 = "0101001010" := by
  decide

@[simp] theorem prefix14_01010010101010_11 : prefixOf "01010010101010" 11 = "01010010101" := by
  decide

@[simp] theorem prefix14_01010010101010_12 : prefixOf "01010010101010" 12 = "010100101010" := by
  decide

@[simp] theorem prefix14_01010010101010_13 : prefixOf "01010010101010" 13 = "0101001010101" := by
  decide

@[simp] theorem prefix14_01010010101010_14 : prefixOf "01010010101010" 14 = "01010010101010" := by
  decide

@[simp] theorem suffix14_01010010101010_7 : suffixFrom "01010010101010" 7 = "0101010" := by
  decide

@[simp] theorem suffix14_01010010101010_8 : suffixFrom "01010010101010" 8 = "101010" := by
  decide

@[simp] theorem suffix14_01010010101010_9 : suffixFrom "01010010101010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_01010010101010_10 : suffixFrom "01010010101010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_01010010101010_11 : suffixFrom "01010010101010" 11 = "010" := by
  decide

@[simp] theorem suffix14_01010010101010_12 : suffixFrom "01010010101010" 12 = "10" := by
  decide

@[simp] theorem prefix14_01010100100100_1 : prefixOf "01010100100100" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010100100100_2 : prefixOf "01010100100100" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010100100100_3 : prefixOf "01010100100100" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010100100100_5 : prefixOf "01010100100100" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010100100100_6 : prefixOf "01010100100100" 6 = "010101" := by
  decide

@[simp] theorem prefix14_01010100100100_7 : prefixOf "01010100100100" 7 = "0101010" := by
  decide

@[simp] theorem prefix14_01010100100100_8 : prefixOf "01010100100100" 8 = "01010100" := by
  decide

@[simp] theorem prefix14_01010100100100_9 : prefixOf "01010100100100" 9 = "010101001" := by
  decide

@[simp] theorem prefix14_01010100100100_10 : prefixOf "01010100100100" 10 = "0101010010" := by
  decide

@[simp] theorem prefix14_01010100100100_11 : prefixOf "01010100100100" 11 = "01010100100" := by
  decide

@[simp] theorem prefix14_01010100100100_12 : prefixOf "01010100100100" 12 = "010101001001" := by
  decide

@[simp] theorem prefix14_01010100100100_13 : prefixOf "01010100100100" 13 = "0101010010010" := by
  decide

@[simp] theorem prefix14_01010100100100_14 : prefixOf "01010100100100" 14 = "01010100100100" := by
  decide

@[simp] theorem suffix14_01010100100100_7 : suffixFrom "01010100100100" 7 = "0100100" := by
  decide

@[simp] theorem suffix14_01010100100100_8 : suffixFrom "01010100100100" 8 = "100100" := by
  decide

@[simp] theorem suffix14_01010100100100_9 : suffixFrom "01010100100100" 9 = "00100" := by
  decide

@[simp] theorem suffix14_01010100100100_10 : suffixFrom "01010100100100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_01010100100100_11 : suffixFrom "01010100100100" 11 = "100" := by
  decide

@[simp] theorem suffix14_01010100100100_12 : suffixFrom "01010100100100" 12 = "00" := by
  decide

@[simp] theorem prefix14_01010100100101_1 : prefixOf "01010100100101" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010100100101_2 : prefixOf "01010100100101" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010100100101_3 : prefixOf "01010100100101" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010100100101_5 : prefixOf "01010100100101" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010100100101_6 : prefixOf "01010100100101" 6 = "010101" := by
  decide

@[simp] theorem prefix14_01010100100101_7 : prefixOf "01010100100101" 7 = "0101010" := by
  decide

@[simp] theorem prefix14_01010100100101_8 : prefixOf "01010100100101" 8 = "01010100" := by
  decide

@[simp] theorem prefix14_01010100100101_9 : prefixOf "01010100100101" 9 = "010101001" := by
  decide

@[simp] theorem prefix14_01010100100101_10 : prefixOf "01010100100101" 10 = "0101010010" := by
  decide

@[simp] theorem prefix14_01010100100101_11 : prefixOf "01010100100101" 11 = "01010100100" := by
  decide

@[simp] theorem prefix14_01010100100101_12 : prefixOf "01010100100101" 12 = "010101001001" := by
  decide

@[simp] theorem prefix14_01010100100101_13 : prefixOf "01010100100101" 13 = "0101010010010" := by
  decide

@[simp] theorem prefix14_01010100100101_14 : prefixOf "01010100100101" 14 = "01010100100101" := by
  decide

@[simp] theorem suffix14_01010100100101_7 : suffixFrom "01010100100101" 7 = "0100101" := by
  decide

@[simp] theorem suffix14_01010100100101_8 : suffixFrom "01010100100101" 8 = "100101" := by
  decide

@[simp] theorem suffix14_01010100100101_9 : suffixFrom "01010100100101" 9 = "00101" := by
  decide

@[simp] theorem suffix14_01010100100101_10 : suffixFrom "01010100100101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_01010100100101_11 : suffixFrom "01010100100101" 11 = "101" := by
  decide

@[simp] theorem suffix14_01010100100101_12 : suffixFrom "01010100100101" 12 = "01" := by
  decide

@[simp] theorem prefix14_01010100101001_1 : prefixOf "01010100101001" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010100101001_2 : prefixOf "01010100101001" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010100101001_3 : prefixOf "01010100101001" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010100101001_5 : prefixOf "01010100101001" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010100101001_6 : prefixOf "01010100101001" 6 = "010101" := by
  decide

@[simp] theorem prefix14_01010100101001_7 : prefixOf "01010100101001" 7 = "0101010" := by
  decide

@[simp] theorem prefix14_01010100101001_8 : prefixOf "01010100101001" 8 = "01010100" := by
  decide

@[simp] theorem prefix14_01010100101001_9 : prefixOf "01010100101001" 9 = "010101001" := by
  decide

@[simp] theorem prefix14_01010100101001_10 : prefixOf "01010100101001" 10 = "0101010010" := by
  decide

@[simp] theorem prefix14_01010100101001_11 : prefixOf "01010100101001" 11 = "01010100101" := by
  decide

@[simp] theorem prefix14_01010100101001_12 : prefixOf "01010100101001" 12 = "010101001010" := by
  decide

@[simp] theorem prefix14_01010100101001_13 : prefixOf "01010100101001" 13 = "0101010010100" := by
  decide

@[simp] theorem prefix14_01010100101001_14 : prefixOf "01010100101001" 14 = "01010100101001" := by
  decide

@[simp] theorem suffix14_01010100101001_7 : suffixFrom "01010100101001" 7 = "0101001" := by
  decide

@[simp] theorem suffix14_01010100101001_8 : suffixFrom "01010100101001" 8 = "101001" := by
  decide

@[simp] theorem suffix14_01010100101001_9 : suffixFrom "01010100101001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_01010100101001_10 : suffixFrom "01010100101001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_01010100101001_11 : suffixFrom "01010100101001" 11 = "001" := by
  decide

@[simp] theorem suffix14_01010100101001_12 : suffixFrom "01010100101001" 12 = "01" := by
  decide

@[simp] theorem prefix14_01010100101010_1 : prefixOf "01010100101010" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010100101010_2 : prefixOf "01010100101010" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010100101010_3 : prefixOf "01010100101010" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010100101010_5 : prefixOf "01010100101010" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010100101010_6 : prefixOf "01010100101010" 6 = "010101" := by
  decide

@[simp] theorem prefix14_01010100101010_7 : prefixOf "01010100101010" 7 = "0101010" := by
  decide

@[simp] theorem prefix14_01010100101010_8 : prefixOf "01010100101010" 8 = "01010100" := by
  decide

@[simp] theorem prefix14_01010100101010_9 : prefixOf "01010100101010" 9 = "010101001" := by
  decide

@[simp] theorem prefix14_01010100101010_10 : prefixOf "01010100101010" 10 = "0101010010" := by
  decide

@[simp] theorem prefix14_01010100101010_11 : prefixOf "01010100101010" 11 = "01010100101" := by
  decide

@[simp] theorem prefix14_01010100101010_12 : prefixOf "01010100101010" 12 = "010101001010" := by
  decide

@[simp] theorem prefix14_01010100101010_13 : prefixOf "01010100101010" 13 = "0101010010101" := by
  decide

@[simp] theorem prefix14_01010100101010_14 : prefixOf "01010100101010" 14 = "01010100101010" := by
  decide

@[simp] theorem suffix14_01010100101010_7 : suffixFrom "01010100101010" 7 = "0101010" := by
  decide

@[simp] theorem suffix14_01010100101010_8 : suffixFrom "01010100101010" 8 = "101010" := by
  decide

@[simp] theorem suffix14_01010100101010_9 : suffixFrom "01010100101010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_01010100101010_10 : suffixFrom "01010100101010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_01010100101010_11 : suffixFrom "01010100101010" 11 = "010" := by
  decide

@[simp] theorem suffix14_01010100101010_12 : suffixFrom "01010100101010" 12 = "10" := by
  decide

@[simp] theorem prefix14_01010101001001_1 : prefixOf "01010101001001" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010101001001_2 : prefixOf "01010101001001" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010101001001_3 : prefixOf "01010101001001" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010101001001_5 : prefixOf "01010101001001" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010101001001_6 : prefixOf "01010101001001" 6 = "010101" := by
  decide

@[simp] theorem prefix14_01010101001001_7 : prefixOf "01010101001001" 7 = "0101010" := by
  decide

@[simp] theorem prefix14_01010101001001_8 : prefixOf "01010101001001" 8 = "01010101" := by
  decide

@[simp] theorem prefix14_01010101001001_9 : prefixOf "01010101001001" 9 = "010101010" := by
  decide

@[simp] theorem prefix14_01010101001001_10 : prefixOf "01010101001001" 10 = "0101010100" := by
  decide

@[simp] theorem prefix14_01010101001001_11 : prefixOf "01010101001001" 11 = "01010101001" := by
  decide

@[simp] theorem prefix14_01010101001001_12 : prefixOf "01010101001001" 12 = "010101010010" := by
  decide

@[simp] theorem prefix14_01010101001001_13 : prefixOf "01010101001001" 13 = "0101010100100" := by
  decide

@[simp] theorem prefix14_01010101001001_14 : prefixOf "01010101001001" 14 = "01010101001001" := by
  decide

@[simp] theorem suffix14_01010101001001_7 : suffixFrom "01010101001001" 7 = "1001001" := by
  decide

@[simp] theorem suffix14_01010101001001_8 : suffixFrom "01010101001001" 8 = "001001" := by
  decide

@[simp] theorem suffix14_01010101001001_9 : suffixFrom "01010101001001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_01010101001001_10 : suffixFrom "01010101001001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_01010101001001_11 : suffixFrom "01010101001001" 11 = "001" := by
  decide

@[simp] theorem suffix14_01010101001001_12 : suffixFrom "01010101001001" 12 = "01" := by
  decide

@[simp] theorem prefix14_01010101001010_1 : prefixOf "01010101001010" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010101001010_2 : prefixOf "01010101001010" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010101001010_3 : prefixOf "01010101001010" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010101001010_5 : prefixOf "01010101001010" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010101001010_6 : prefixOf "01010101001010" 6 = "010101" := by
  decide

@[simp] theorem prefix14_01010101001010_7 : prefixOf "01010101001010" 7 = "0101010" := by
  decide

@[simp] theorem prefix14_01010101001010_8 : prefixOf "01010101001010" 8 = "01010101" := by
  decide

@[simp] theorem prefix14_01010101001010_9 : prefixOf "01010101001010" 9 = "010101010" := by
  decide

@[simp] theorem prefix14_01010101001010_10 : prefixOf "01010101001010" 10 = "0101010100" := by
  decide

@[simp] theorem prefix14_01010101001010_11 : prefixOf "01010101001010" 11 = "01010101001" := by
  decide

@[simp] theorem prefix14_01010101001010_12 : prefixOf "01010101001010" 12 = "010101010010" := by
  decide

@[simp] theorem prefix14_01010101001010_13 : prefixOf "01010101001010" 13 = "0101010100101" := by
  decide

@[simp] theorem prefix14_01010101001010_14 : prefixOf "01010101001010" 14 = "01010101001010" := by
  decide

@[simp] theorem suffix14_01010101001010_7 : suffixFrom "01010101001010" 7 = "1001010" := by
  decide

@[simp] theorem suffix14_01010101001010_8 : suffixFrom "01010101001010" 8 = "001010" := by
  decide

@[simp] theorem suffix14_01010101001010_9 : suffixFrom "01010101001010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_01010101001010_10 : suffixFrom "01010101001010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_01010101001010_11 : suffixFrom "01010101001010" 11 = "010" := by
  decide

@[simp] theorem suffix14_01010101001010_12 : suffixFrom "01010101001010" 12 = "10" := by
  decide

@[simp] theorem prefix14_01010101010010_1 : prefixOf "01010101010010" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010101010010_2 : prefixOf "01010101010010" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010101010010_3 : prefixOf "01010101010010" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010101010010_5 : prefixOf "01010101010010" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010101010010_6 : prefixOf "01010101010010" 6 = "010101" := by
  decide

@[simp] theorem prefix14_01010101010010_7 : prefixOf "01010101010010" 7 = "0101010" := by
  decide

@[simp] theorem prefix14_01010101010010_8 : prefixOf "01010101010010" 8 = "01010101" := by
  decide

@[simp] theorem prefix14_01010101010010_9 : prefixOf "01010101010010" 9 = "010101010" := by
  decide

@[simp] theorem prefix14_01010101010010_10 : prefixOf "01010101010010" 10 = "0101010101" := by
  decide

@[simp] theorem prefix14_01010101010010_11 : prefixOf "01010101010010" 11 = "01010101010" := by
  decide

@[simp] theorem prefix14_01010101010010_12 : prefixOf "01010101010010" 12 = "010101010100" := by
  decide

@[simp] theorem prefix14_01010101010010_13 : prefixOf "01010101010010" 13 = "0101010101001" := by
  decide

@[simp] theorem prefix14_01010101010010_14 : prefixOf "01010101010010" 14 = "01010101010010" := by
  decide

@[simp] theorem suffix14_01010101010010_7 : suffixFrom "01010101010010" 7 = "1010010" := by
  decide

@[simp] theorem suffix14_01010101010010_8 : suffixFrom "01010101010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_01010101010010_9 : suffixFrom "01010101010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_01010101010010_10 : suffixFrom "01010101010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_01010101010010_11 : suffixFrom "01010101010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_01010101010010_12 : suffixFrom "01010101010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_01010101010100_1 : prefixOf "01010101010100" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010101010100_2 : prefixOf "01010101010100" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010101010100_3 : prefixOf "01010101010100" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010101010100_5 : prefixOf "01010101010100" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010101010100_6 : prefixOf "01010101010100" 6 = "010101" := by
  decide

@[simp] theorem prefix14_01010101010100_7 : prefixOf "01010101010100" 7 = "0101010" := by
  decide

@[simp] theorem prefix14_01010101010100_8 : prefixOf "01010101010100" 8 = "01010101" := by
  decide

@[simp] theorem prefix14_01010101010100_9 : prefixOf "01010101010100" 9 = "010101010" := by
  decide

@[simp] theorem prefix14_01010101010100_10 : prefixOf "01010101010100" 10 = "0101010101" := by
  decide

@[simp] theorem prefix14_01010101010100_11 : prefixOf "01010101010100" 11 = "01010101010" := by
  decide

@[simp] theorem prefix14_01010101010100_12 : prefixOf "01010101010100" 12 = "010101010101" := by
  decide

@[simp] theorem prefix14_01010101010100_13 : prefixOf "01010101010100" 13 = "0101010101010" := by
  decide

@[simp] theorem prefix14_01010101010100_14 : prefixOf "01010101010100" 14 = "01010101010100" := by
  decide

@[simp] theorem suffix14_01010101010100_7 : suffixFrom "01010101010100" 7 = "1010100" := by
  decide

@[simp] theorem suffix14_01010101010100_8 : suffixFrom "01010101010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_01010101010100_9 : suffixFrom "01010101010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_01010101010100_10 : suffixFrom "01010101010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_01010101010100_11 : suffixFrom "01010101010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_01010101010100_12 : suffixFrom "01010101010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_01010101010101_1 : prefixOf "01010101010101" 1 = "0" := by
  decide

@[simp] theorem prefix14_01010101010101_2 : prefixOf "01010101010101" 2 = "01" := by
  decide

@[simp] theorem prefix14_01010101010101_3 : prefixOf "01010101010101" 3 = "010" := by
  decide

@[simp] theorem prefix14_01010101010101_5 : prefixOf "01010101010101" 5 = "01010" := by
  decide

@[simp] theorem prefix14_01010101010101_6 : prefixOf "01010101010101" 6 = "010101" := by
  decide

@[simp] theorem prefix14_01010101010101_7 : prefixOf "01010101010101" 7 = "0101010" := by
  decide

@[simp] theorem prefix14_01010101010101_8 : prefixOf "01010101010101" 8 = "01010101" := by
  decide

@[simp] theorem prefix14_01010101010101_9 : prefixOf "01010101010101" 9 = "010101010" := by
  decide

@[simp] theorem prefix14_01010101010101_10 : prefixOf "01010101010101" 10 = "0101010101" := by
  decide

@[simp] theorem prefix14_01010101010101_11 : prefixOf "01010101010101" 11 = "01010101010" := by
  decide

@[simp] theorem prefix14_01010101010101_12 : prefixOf "01010101010101" 12 = "010101010101" := by
  decide

@[simp] theorem prefix14_01010101010101_13 : prefixOf "01010101010101" 13 = "0101010101010" := by
  decide

@[simp] theorem prefix14_01010101010101_14 : prefixOf "01010101010101" 14 = "01010101010101" := by
  decide

@[simp] theorem suffix14_01010101010101_7 : suffixFrom "01010101010101" 7 = "1010101" := by
  decide

@[simp] theorem suffix14_01010101010101_8 : suffixFrom "01010101010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_01010101010101_9 : suffixFrom "01010101010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_01010101010101_10 : suffixFrom "01010101010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_01010101010101_11 : suffixFrom "01010101010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_01010101010101_12 : suffixFrom "01010101010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_10010010010010_1 : prefixOf "10010010010010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010010010010_2 : prefixOf "10010010010010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010010010010_3 : prefixOf "10010010010010" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010010010010_5 : prefixOf "10010010010010" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010010010010_6 : prefixOf "10010010010010" 6 = "100100" := by
  decide

@[simp] theorem prefix14_10010010010010_7 : prefixOf "10010010010010" 7 = "1001001" := by
  decide

@[simp] theorem prefix14_10010010010010_8 : prefixOf "10010010010010" 8 = "10010010" := by
  decide

@[simp] theorem prefix14_10010010010010_9 : prefixOf "10010010010010" 9 = "100100100" := by
  decide

@[simp] theorem prefix14_10010010010010_10 : prefixOf "10010010010010" 10 = "1001001001" := by
  decide

@[simp] theorem prefix14_10010010010010_11 : prefixOf "10010010010010" 11 = "10010010010" := by
  decide

@[simp] theorem prefix14_10010010010010_12 : prefixOf "10010010010010" 12 = "100100100100" := by
  decide

@[simp] theorem prefix14_10010010010010_13 : prefixOf "10010010010010" 13 = "1001001001001" := by
  decide

@[simp] theorem prefix14_10010010010010_14 : prefixOf "10010010010010" 14 = "10010010010010" := by
  decide

@[simp] theorem suffix14_10010010010010_7 : suffixFrom "10010010010010" 7 = "0010010" := by
  decide

@[simp] theorem suffix14_10010010010010_8 : suffixFrom "10010010010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_10010010010010_9 : suffixFrom "10010010010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_10010010010010_10 : suffixFrom "10010010010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_10010010010010_11 : suffixFrom "10010010010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10010010010010_12 : suffixFrom "10010010010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10010010010100_1 : prefixOf "10010010010100" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010010010100_2 : prefixOf "10010010010100" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010010010100_3 : prefixOf "10010010010100" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010010010100_5 : prefixOf "10010010010100" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010010010100_6 : prefixOf "10010010010100" 6 = "100100" := by
  decide

@[simp] theorem prefix14_10010010010100_7 : prefixOf "10010010010100" 7 = "1001001" := by
  decide

@[simp] theorem prefix14_10010010010100_8 : prefixOf "10010010010100" 8 = "10010010" := by
  decide

@[simp] theorem prefix14_10010010010100_9 : prefixOf "10010010010100" 9 = "100100100" := by
  decide

@[simp] theorem prefix14_10010010010100_10 : prefixOf "10010010010100" 10 = "1001001001" := by
  decide

@[simp] theorem prefix14_10010010010100_11 : prefixOf "10010010010100" 11 = "10010010010" := by
  decide

@[simp] theorem prefix14_10010010010100_12 : prefixOf "10010010010100" 12 = "100100100101" := by
  decide

@[simp] theorem prefix14_10010010010100_13 : prefixOf "10010010010100" 13 = "1001001001010" := by
  decide

@[simp] theorem prefix14_10010010010100_14 : prefixOf "10010010010100" 14 = "10010010010100" := by
  decide

@[simp] theorem suffix14_10010010010100_7 : suffixFrom "10010010010100" 7 = "0010100" := by
  decide

@[simp] theorem suffix14_10010010010100_8 : suffixFrom "10010010010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_10010010010100_9 : suffixFrom "10010010010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_10010010010100_10 : suffixFrom "10010010010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_10010010010100_11 : suffixFrom "10010010010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_10010010010100_12 : suffixFrom "10010010010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_10010010010101_1 : prefixOf "10010010010101" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010010010101_2 : prefixOf "10010010010101" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010010010101_3 : prefixOf "10010010010101" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010010010101_5 : prefixOf "10010010010101" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010010010101_6 : prefixOf "10010010010101" 6 = "100100" := by
  decide

@[simp] theorem prefix14_10010010010101_7 : prefixOf "10010010010101" 7 = "1001001" := by
  decide

@[simp] theorem prefix14_10010010010101_8 : prefixOf "10010010010101" 8 = "10010010" := by
  decide

@[simp] theorem prefix14_10010010010101_9 : prefixOf "10010010010101" 9 = "100100100" := by
  decide

@[simp] theorem prefix14_10010010010101_10 : prefixOf "10010010010101" 10 = "1001001001" := by
  decide

@[simp] theorem prefix14_10010010010101_11 : prefixOf "10010010010101" 11 = "10010010010" := by
  decide

@[simp] theorem prefix14_10010010010101_12 : prefixOf "10010010010101" 12 = "100100100101" := by
  decide

@[simp] theorem prefix14_10010010010101_13 : prefixOf "10010010010101" 13 = "1001001001010" := by
  decide

@[simp] theorem prefix14_10010010010101_14 : prefixOf "10010010010101" 14 = "10010010010101" := by
  decide

@[simp] theorem suffix14_10010010010101_7 : suffixFrom "10010010010101" 7 = "0010101" := by
  decide

@[simp] theorem suffix14_10010010010101_8 : suffixFrom "10010010010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_10010010010101_9 : suffixFrom "10010010010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_10010010010101_10 : suffixFrom "10010010010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_10010010010101_11 : suffixFrom "10010010010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_10010010010101_12 : suffixFrom "10010010010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_10010010100100_1 : prefixOf "10010010100100" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010010100100_2 : prefixOf "10010010100100" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010010100100_3 : prefixOf "10010010100100" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010010100100_5 : prefixOf "10010010100100" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010010100100_6 : prefixOf "10010010100100" 6 = "100100" := by
  decide

@[simp] theorem prefix14_10010010100100_7 : prefixOf "10010010100100" 7 = "1001001" := by
  decide

@[simp] theorem prefix14_10010010100100_8 : prefixOf "10010010100100" 8 = "10010010" := by
  decide

@[simp] theorem prefix14_10010010100100_9 : prefixOf "10010010100100" 9 = "100100101" := by
  decide

@[simp] theorem prefix14_10010010100100_10 : prefixOf "10010010100100" 10 = "1001001010" := by
  decide

@[simp] theorem prefix14_10010010100100_11 : prefixOf "10010010100100" 11 = "10010010100" := by
  decide

@[simp] theorem prefix14_10010010100100_12 : prefixOf "10010010100100" 12 = "100100101001" := by
  decide

@[simp] theorem prefix14_10010010100100_13 : prefixOf "10010010100100" 13 = "1001001010010" := by
  decide

@[simp] theorem prefix14_10010010100100_14 : prefixOf "10010010100100" 14 = "10010010100100" := by
  decide

@[simp] theorem suffix14_10010010100100_7 : suffixFrom "10010010100100" 7 = "0100100" := by
  decide

@[simp] theorem suffix14_10010010100100_8 : suffixFrom "10010010100100" 8 = "100100" := by
  decide

@[simp] theorem suffix14_10010010100100_9 : suffixFrom "10010010100100" 9 = "00100" := by
  decide

@[simp] theorem suffix14_10010010100100_10 : suffixFrom "10010010100100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_10010010100100_11 : suffixFrom "10010010100100" 11 = "100" := by
  decide

@[simp] theorem suffix14_10010010100100_12 : suffixFrom "10010010100100" 12 = "00" := by
  decide

@[simp] theorem prefix14_10010010100101_1 : prefixOf "10010010100101" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010010100101_2 : prefixOf "10010010100101" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010010100101_3 : prefixOf "10010010100101" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010010100101_5 : prefixOf "10010010100101" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010010100101_6 : prefixOf "10010010100101" 6 = "100100" := by
  decide

@[simp] theorem prefix14_10010010100101_7 : prefixOf "10010010100101" 7 = "1001001" := by
  decide

@[simp] theorem prefix14_10010010100101_8 : prefixOf "10010010100101" 8 = "10010010" := by
  decide

@[simp] theorem prefix14_10010010100101_9 : prefixOf "10010010100101" 9 = "100100101" := by
  decide

@[simp] theorem prefix14_10010010100101_10 : prefixOf "10010010100101" 10 = "1001001010" := by
  decide

@[simp] theorem prefix14_10010010100101_11 : prefixOf "10010010100101" 11 = "10010010100" := by
  decide

@[simp] theorem prefix14_10010010100101_12 : prefixOf "10010010100101" 12 = "100100101001" := by
  decide

@[simp] theorem prefix14_10010010100101_13 : prefixOf "10010010100101" 13 = "1001001010010" := by
  decide

@[simp] theorem prefix14_10010010100101_14 : prefixOf "10010010100101" 14 = "10010010100101" := by
  decide

@[simp] theorem suffix14_10010010100101_7 : suffixFrom "10010010100101" 7 = "0100101" := by
  decide

@[simp] theorem suffix14_10010010100101_8 : suffixFrom "10010010100101" 8 = "100101" := by
  decide

@[simp] theorem suffix14_10010010100101_9 : suffixFrom "10010010100101" 9 = "00101" := by
  decide

@[simp] theorem suffix14_10010010100101_10 : suffixFrom "10010010100101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_10010010100101_11 : suffixFrom "10010010100101" 11 = "101" := by
  decide

@[simp] theorem suffix14_10010010100101_12 : suffixFrom "10010010100101" 12 = "01" := by
  decide

@[simp] theorem prefix14_10010010101001_1 : prefixOf "10010010101001" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010010101001_2 : prefixOf "10010010101001" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010010101001_3 : prefixOf "10010010101001" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010010101001_5 : prefixOf "10010010101001" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010010101001_6 : prefixOf "10010010101001" 6 = "100100" := by
  decide

@[simp] theorem prefix14_10010010101001_7 : prefixOf "10010010101001" 7 = "1001001" := by
  decide

@[simp] theorem prefix14_10010010101001_8 : prefixOf "10010010101001" 8 = "10010010" := by
  decide

@[simp] theorem prefix14_10010010101001_9 : prefixOf "10010010101001" 9 = "100100101" := by
  decide

@[simp] theorem prefix14_10010010101001_10 : prefixOf "10010010101001" 10 = "1001001010" := by
  decide

@[simp] theorem prefix14_10010010101001_11 : prefixOf "10010010101001" 11 = "10010010101" := by
  decide

@[simp] theorem prefix14_10010010101001_12 : prefixOf "10010010101001" 12 = "100100101010" := by
  decide

@[simp] theorem prefix14_10010010101001_13 : prefixOf "10010010101001" 13 = "1001001010100" := by
  decide

@[simp] theorem prefix14_10010010101001_14 : prefixOf "10010010101001" 14 = "10010010101001" := by
  decide

@[simp] theorem suffix14_10010010101001_7 : suffixFrom "10010010101001" 7 = "0101001" := by
  decide

@[simp] theorem suffix14_10010010101001_8 : suffixFrom "10010010101001" 8 = "101001" := by
  decide

@[simp] theorem suffix14_10010010101001_9 : suffixFrom "10010010101001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_10010010101001_10 : suffixFrom "10010010101001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_10010010101001_11 : suffixFrom "10010010101001" 11 = "001" := by
  decide

@[simp] theorem suffix14_10010010101001_12 : suffixFrom "10010010101001" 12 = "01" := by
  decide

@[simp] theorem prefix14_10010010101010_1 : prefixOf "10010010101010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010010101010_2 : prefixOf "10010010101010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010010101010_3 : prefixOf "10010010101010" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010010101010_5 : prefixOf "10010010101010" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010010101010_6 : prefixOf "10010010101010" 6 = "100100" := by
  decide

@[simp] theorem prefix14_10010010101010_7 : prefixOf "10010010101010" 7 = "1001001" := by
  decide

@[simp] theorem prefix14_10010010101010_8 : prefixOf "10010010101010" 8 = "10010010" := by
  decide

@[simp] theorem prefix14_10010010101010_9 : prefixOf "10010010101010" 9 = "100100101" := by
  decide

@[simp] theorem prefix14_10010010101010_10 : prefixOf "10010010101010" 10 = "1001001010" := by
  decide

@[simp] theorem prefix14_10010010101010_11 : prefixOf "10010010101010" 11 = "10010010101" := by
  decide

@[simp] theorem prefix14_10010010101010_12 : prefixOf "10010010101010" 12 = "100100101010" := by
  decide

@[simp] theorem prefix14_10010010101010_13 : prefixOf "10010010101010" 13 = "1001001010101" := by
  decide

@[simp] theorem prefix14_10010010101010_14 : prefixOf "10010010101010" 14 = "10010010101010" := by
  decide

@[simp] theorem suffix14_10010010101010_7 : suffixFrom "10010010101010" 7 = "0101010" := by
  decide

@[simp] theorem suffix14_10010010101010_8 : suffixFrom "10010010101010" 8 = "101010" := by
  decide

@[simp] theorem suffix14_10010010101010_9 : suffixFrom "10010010101010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_10010010101010_10 : suffixFrom "10010010101010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_10010010101010_11 : suffixFrom "10010010101010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10010010101010_12 : suffixFrom "10010010101010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10010100100100_1 : prefixOf "10010100100100" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010100100100_2 : prefixOf "10010100100100" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010100100100_3 : prefixOf "10010100100100" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010100100100_5 : prefixOf "10010100100100" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010100100100_6 : prefixOf "10010100100100" 6 = "100101" := by
  decide

@[simp] theorem prefix14_10010100100100_7 : prefixOf "10010100100100" 7 = "1001010" := by
  decide

@[simp] theorem prefix14_10010100100100_8 : prefixOf "10010100100100" 8 = "10010100" := by
  decide

@[simp] theorem prefix14_10010100100100_9 : prefixOf "10010100100100" 9 = "100101001" := by
  decide

@[simp] theorem prefix14_10010100100100_10 : prefixOf "10010100100100" 10 = "1001010010" := by
  decide

@[simp] theorem prefix14_10010100100100_11 : prefixOf "10010100100100" 11 = "10010100100" := by
  decide

@[simp] theorem prefix14_10010100100100_12 : prefixOf "10010100100100" 12 = "100101001001" := by
  decide

@[simp] theorem prefix14_10010100100100_13 : prefixOf "10010100100100" 13 = "1001010010010" := by
  decide

@[simp] theorem prefix14_10010100100100_14 : prefixOf "10010100100100" 14 = "10010100100100" := by
  decide

@[simp] theorem suffix14_10010100100100_7 : suffixFrom "10010100100100" 7 = "0100100" := by
  decide

@[simp] theorem suffix14_10010100100100_8 : suffixFrom "10010100100100" 8 = "100100" := by
  decide

@[simp] theorem suffix14_10010100100100_9 : suffixFrom "10010100100100" 9 = "00100" := by
  decide

@[simp] theorem suffix14_10010100100100_10 : suffixFrom "10010100100100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_10010100100100_11 : suffixFrom "10010100100100" 11 = "100" := by
  decide

@[simp] theorem suffix14_10010100100100_12 : suffixFrom "10010100100100" 12 = "00" := by
  decide

@[simp] theorem prefix14_10010100100101_1 : prefixOf "10010100100101" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010100100101_2 : prefixOf "10010100100101" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010100100101_3 : prefixOf "10010100100101" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010100100101_5 : prefixOf "10010100100101" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010100100101_6 : prefixOf "10010100100101" 6 = "100101" := by
  decide

@[simp] theorem prefix14_10010100100101_7 : prefixOf "10010100100101" 7 = "1001010" := by
  decide

@[simp] theorem prefix14_10010100100101_8 : prefixOf "10010100100101" 8 = "10010100" := by
  decide

@[simp] theorem prefix14_10010100100101_9 : prefixOf "10010100100101" 9 = "100101001" := by
  decide

@[simp] theorem prefix14_10010100100101_10 : prefixOf "10010100100101" 10 = "1001010010" := by
  decide

@[simp] theorem prefix14_10010100100101_11 : prefixOf "10010100100101" 11 = "10010100100" := by
  decide

@[simp] theorem prefix14_10010100100101_12 : prefixOf "10010100100101" 12 = "100101001001" := by
  decide

@[simp] theorem prefix14_10010100100101_13 : prefixOf "10010100100101" 13 = "1001010010010" := by
  decide

@[simp] theorem prefix14_10010100100101_14 : prefixOf "10010100100101" 14 = "10010100100101" := by
  decide

@[simp] theorem suffix14_10010100100101_7 : suffixFrom "10010100100101" 7 = "0100101" := by
  decide

@[simp] theorem suffix14_10010100100101_8 : suffixFrom "10010100100101" 8 = "100101" := by
  decide

@[simp] theorem suffix14_10010100100101_9 : suffixFrom "10010100100101" 9 = "00101" := by
  decide

@[simp] theorem suffix14_10010100100101_10 : suffixFrom "10010100100101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_10010100100101_11 : suffixFrom "10010100100101" 11 = "101" := by
  decide

@[simp] theorem suffix14_10010100100101_12 : suffixFrom "10010100100101" 12 = "01" := by
  decide

@[simp] theorem prefix14_10010100101001_1 : prefixOf "10010100101001" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010100101001_2 : prefixOf "10010100101001" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010100101001_3 : prefixOf "10010100101001" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010100101001_5 : prefixOf "10010100101001" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010100101001_6 : prefixOf "10010100101001" 6 = "100101" := by
  decide

@[simp] theorem prefix14_10010100101001_7 : prefixOf "10010100101001" 7 = "1001010" := by
  decide

@[simp] theorem prefix14_10010100101001_8 : prefixOf "10010100101001" 8 = "10010100" := by
  decide

@[simp] theorem prefix14_10010100101001_9 : prefixOf "10010100101001" 9 = "100101001" := by
  decide

@[simp] theorem prefix14_10010100101001_10 : prefixOf "10010100101001" 10 = "1001010010" := by
  decide

@[simp] theorem prefix14_10010100101001_11 : prefixOf "10010100101001" 11 = "10010100101" := by
  decide

@[simp] theorem prefix14_10010100101001_12 : prefixOf "10010100101001" 12 = "100101001010" := by
  decide

@[simp] theorem prefix14_10010100101001_13 : prefixOf "10010100101001" 13 = "1001010010100" := by
  decide

@[simp] theorem prefix14_10010100101001_14 : prefixOf "10010100101001" 14 = "10010100101001" := by
  decide

@[simp] theorem suffix14_10010100101001_7 : suffixFrom "10010100101001" 7 = "0101001" := by
  decide

@[simp] theorem suffix14_10010100101001_8 : suffixFrom "10010100101001" 8 = "101001" := by
  decide

@[simp] theorem suffix14_10010100101001_9 : suffixFrom "10010100101001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_10010100101001_10 : suffixFrom "10010100101001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_10010100101001_11 : suffixFrom "10010100101001" 11 = "001" := by
  decide

@[simp] theorem suffix14_10010100101001_12 : suffixFrom "10010100101001" 12 = "01" := by
  decide

@[simp] theorem prefix14_10010100101010_1 : prefixOf "10010100101010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010100101010_2 : prefixOf "10010100101010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010100101010_3 : prefixOf "10010100101010" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010100101010_5 : prefixOf "10010100101010" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010100101010_6 : prefixOf "10010100101010" 6 = "100101" := by
  decide

@[simp] theorem prefix14_10010100101010_7 : prefixOf "10010100101010" 7 = "1001010" := by
  decide

@[simp] theorem prefix14_10010100101010_8 : prefixOf "10010100101010" 8 = "10010100" := by
  decide

@[simp] theorem prefix14_10010100101010_9 : prefixOf "10010100101010" 9 = "100101001" := by
  decide

@[simp] theorem prefix14_10010100101010_10 : prefixOf "10010100101010" 10 = "1001010010" := by
  decide

@[simp] theorem prefix14_10010100101010_11 : prefixOf "10010100101010" 11 = "10010100101" := by
  decide

@[simp] theorem prefix14_10010100101010_12 : prefixOf "10010100101010" 12 = "100101001010" := by
  decide

@[simp] theorem prefix14_10010100101010_13 : prefixOf "10010100101010" 13 = "1001010010101" := by
  decide

@[simp] theorem prefix14_10010100101010_14 : prefixOf "10010100101010" 14 = "10010100101010" := by
  decide

@[simp] theorem suffix14_10010100101010_7 : suffixFrom "10010100101010" 7 = "0101010" := by
  decide

@[simp] theorem suffix14_10010100101010_8 : suffixFrom "10010100101010" 8 = "101010" := by
  decide

@[simp] theorem suffix14_10010100101010_9 : suffixFrom "10010100101010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_10010100101010_10 : suffixFrom "10010100101010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_10010100101010_11 : suffixFrom "10010100101010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10010100101010_12 : suffixFrom "10010100101010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10010101001001_1 : prefixOf "10010101001001" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010101001001_2 : prefixOf "10010101001001" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010101001001_3 : prefixOf "10010101001001" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010101001001_5 : prefixOf "10010101001001" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010101001001_6 : prefixOf "10010101001001" 6 = "100101" := by
  decide

@[simp] theorem prefix14_10010101001001_7 : prefixOf "10010101001001" 7 = "1001010" := by
  decide

@[simp] theorem prefix14_10010101001001_8 : prefixOf "10010101001001" 8 = "10010101" := by
  decide

@[simp] theorem prefix14_10010101001001_9 : prefixOf "10010101001001" 9 = "100101010" := by
  decide

@[simp] theorem prefix14_10010101001001_10 : prefixOf "10010101001001" 10 = "1001010100" := by
  decide

@[simp] theorem prefix14_10010101001001_11 : prefixOf "10010101001001" 11 = "10010101001" := by
  decide

@[simp] theorem prefix14_10010101001001_12 : prefixOf "10010101001001" 12 = "100101010010" := by
  decide

@[simp] theorem prefix14_10010101001001_13 : prefixOf "10010101001001" 13 = "1001010100100" := by
  decide

@[simp] theorem prefix14_10010101001001_14 : prefixOf "10010101001001" 14 = "10010101001001" := by
  decide

@[simp] theorem suffix14_10010101001001_7 : suffixFrom "10010101001001" 7 = "1001001" := by
  decide

@[simp] theorem suffix14_10010101001001_8 : suffixFrom "10010101001001" 8 = "001001" := by
  decide

@[simp] theorem suffix14_10010101001001_9 : suffixFrom "10010101001001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_10010101001001_10 : suffixFrom "10010101001001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_10010101001001_11 : suffixFrom "10010101001001" 11 = "001" := by
  decide

@[simp] theorem suffix14_10010101001001_12 : suffixFrom "10010101001001" 12 = "01" := by
  decide

@[simp] theorem prefix14_10010101001010_1 : prefixOf "10010101001010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010101001010_2 : prefixOf "10010101001010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010101001010_3 : prefixOf "10010101001010" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010101001010_5 : prefixOf "10010101001010" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010101001010_6 : prefixOf "10010101001010" 6 = "100101" := by
  decide

@[simp] theorem prefix14_10010101001010_7 : prefixOf "10010101001010" 7 = "1001010" := by
  decide

@[simp] theorem prefix14_10010101001010_8 : prefixOf "10010101001010" 8 = "10010101" := by
  decide

@[simp] theorem prefix14_10010101001010_9 : prefixOf "10010101001010" 9 = "100101010" := by
  decide

@[simp] theorem prefix14_10010101001010_10 : prefixOf "10010101001010" 10 = "1001010100" := by
  decide

@[simp] theorem prefix14_10010101001010_11 : prefixOf "10010101001010" 11 = "10010101001" := by
  decide

@[simp] theorem prefix14_10010101001010_12 : prefixOf "10010101001010" 12 = "100101010010" := by
  decide

@[simp] theorem prefix14_10010101001010_13 : prefixOf "10010101001010" 13 = "1001010100101" := by
  decide

@[simp] theorem prefix14_10010101001010_14 : prefixOf "10010101001010" 14 = "10010101001010" := by
  decide

@[simp] theorem suffix14_10010101001010_7 : suffixFrom "10010101001010" 7 = "1001010" := by
  decide

@[simp] theorem suffix14_10010101001010_8 : suffixFrom "10010101001010" 8 = "001010" := by
  decide

@[simp] theorem suffix14_10010101001010_9 : suffixFrom "10010101001010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_10010101001010_10 : suffixFrom "10010101001010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_10010101001010_11 : suffixFrom "10010101001010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10010101001010_12 : suffixFrom "10010101001010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10010101010010_1 : prefixOf "10010101010010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010101010010_2 : prefixOf "10010101010010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010101010010_3 : prefixOf "10010101010010" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010101010010_5 : prefixOf "10010101010010" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010101010010_6 : prefixOf "10010101010010" 6 = "100101" := by
  decide

@[simp] theorem prefix14_10010101010010_7 : prefixOf "10010101010010" 7 = "1001010" := by
  decide

@[simp] theorem prefix14_10010101010010_8 : prefixOf "10010101010010" 8 = "10010101" := by
  decide

@[simp] theorem prefix14_10010101010010_9 : prefixOf "10010101010010" 9 = "100101010" := by
  decide

@[simp] theorem prefix14_10010101010010_10 : prefixOf "10010101010010" 10 = "1001010101" := by
  decide

@[simp] theorem prefix14_10010101010010_11 : prefixOf "10010101010010" 11 = "10010101010" := by
  decide

@[simp] theorem prefix14_10010101010010_12 : prefixOf "10010101010010" 12 = "100101010100" := by
  decide

@[simp] theorem prefix14_10010101010010_13 : prefixOf "10010101010010" 13 = "1001010101001" := by
  decide

@[simp] theorem prefix14_10010101010010_14 : prefixOf "10010101010010" 14 = "10010101010010" := by
  decide

@[simp] theorem suffix14_10010101010010_7 : suffixFrom "10010101010010" 7 = "1010010" := by
  decide

@[simp] theorem suffix14_10010101010010_8 : suffixFrom "10010101010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_10010101010010_9 : suffixFrom "10010101010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_10010101010010_10 : suffixFrom "10010101010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_10010101010010_11 : suffixFrom "10010101010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10010101010010_12 : suffixFrom "10010101010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10010101010100_1 : prefixOf "10010101010100" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010101010100_2 : prefixOf "10010101010100" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010101010100_3 : prefixOf "10010101010100" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010101010100_5 : prefixOf "10010101010100" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010101010100_6 : prefixOf "10010101010100" 6 = "100101" := by
  decide

@[simp] theorem prefix14_10010101010100_7 : prefixOf "10010101010100" 7 = "1001010" := by
  decide

@[simp] theorem prefix14_10010101010100_8 : prefixOf "10010101010100" 8 = "10010101" := by
  decide

@[simp] theorem prefix14_10010101010100_9 : prefixOf "10010101010100" 9 = "100101010" := by
  decide

@[simp] theorem prefix14_10010101010100_10 : prefixOf "10010101010100" 10 = "1001010101" := by
  decide

@[simp] theorem prefix14_10010101010100_11 : prefixOf "10010101010100" 11 = "10010101010" := by
  decide

@[simp] theorem prefix14_10010101010100_12 : prefixOf "10010101010100" 12 = "100101010101" := by
  decide

@[simp] theorem prefix14_10010101010100_13 : prefixOf "10010101010100" 13 = "1001010101010" := by
  decide

@[simp] theorem prefix14_10010101010100_14 : prefixOf "10010101010100" 14 = "10010101010100" := by
  decide

@[simp] theorem suffix14_10010101010100_7 : suffixFrom "10010101010100" 7 = "1010100" := by
  decide

@[simp] theorem suffix14_10010101010100_8 : suffixFrom "10010101010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_10010101010100_9 : suffixFrom "10010101010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_10010101010100_10 : suffixFrom "10010101010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_10010101010100_11 : suffixFrom "10010101010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_10010101010100_12 : suffixFrom "10010101010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_10010101010101_1 : prefixOf "10010101010101" 1 = "1" := by
  decide

@[simp] theorem prefix14_10010101010101_2 : prefixOf "10010101010101" 2 = "10" := by
  decide

@[simp] theorem prefix14_10010101010101_3 : prefixOf "10010101010101" 3 = "100" := by
  decide

@[simp] theorem prefix14_10010101010101_5 : prefixOf "10010101010101" 5 = "10010" := by
  decide

@[simp] theorem prefix14_10010101010101_6 : prefixOf "10010101010101" 6 = "100101" := by
  decide

@[simp] theorem prefix14_10010101010101_7 : prefixOf "10010101010101" 7 = "1001010" := by
  decide

@[simp] theorem prefix14_10010101010101_8 : prefixOf "10010101010101" 8 = "10010101" := by
  decide

@[simp] theorem prefix14_10010101010101_9 : prefixOf "10010101010101" 9 = "100101010" := by
  decide

@[simp] theorem prefix14_10010101010101_10 : prefixOf "10010101010101" 10 = "1001010101" := by
  decide

@[simp] theorem prefix14_10010101010101_11 : prefixOf "10010101010101" 11 = "10010101010" := by
  decide

@[simp] theorem prefix14_10010101010101_12 : prefixOf "10010101010101" 12 = "100101010101" := by
  decide

@[simp] theorem prefix14_10010101010101_13 : prefixOf "10010101010101" 13 = "1001010101010" := by
  decide

@[simp] theorem prefix14_10010101010101_14 : prefixOf "10010101010101" 14 = "10010101010101" := by
  decide

@[simp] theorem suffix14_10010101010101_7 : suffixFrom "10010101010101" 7 = "1010101" := by
  decide

@[simp] theorem suffix14_10010101010101_8 : suffixFrom "10010101010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_10010101010101_9 : suffixFrom "10010101010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_10010101010101_10 : suffixFrom "10010101010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_10010101010101_11 : suffixFrom "10010101010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_10010101010101_12 : suffixFrom "10010101010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_10100100100100_1 : prefixOf "10100100100100" 1 = "1" := by
  decide

@[simp] theorem prefix14_10100100100100_2 : prefixOf "10100100100100" 2 = "10" := by
  decide

@[simp] theorem prefix14_10100100100100_3 : prefixOf "10100100100100" 3 = "101" := by
  decide

@[simp] theorem prefix14_10100100100100_5 : prefixOf "10100100100100" 5 = "10100" := by
  decide

@[simp] theorem prefix14_10100100100100_6 : prefixOf "10100100100100" 6 = "101001" := by
  decide

@[simp] theorem prefix14_10100100100100_7 : prefixOf "10100100100100" 7 = "1010010" := by
  decide

@[simp] theorem prefix14_10100100100100_8 : prefixOf "10100100100100" 8 = "10100100" := by
  decide

@[simp] theorem prefix14_10100100100100_9 : prefixOf "10100100100100" 9 = "101001001" := by
  decide

@[simp] theorem prefix14_10100100100100_10 : prefixOf "10100100100100" 10 = "1010010010" := by
  decide

@[simp] theorem prefix14_10100100100100_11 : prefixOf "10100100100100" 11 = "10100100100" := by
  decide

@[simp] theorem prefix14_10100100100100_12 : prefixOf "10100100100100" 12 = "101001001001" := by
  decide

@[simp] theorem prefix14_10100100100100_13 : prefixOf "10100100100100" 13 = "1010010010010" := by
  decide

@[simp] theorem prefix14_10100100100100_14 : prefixOf "10100100100100" 14 = "10100100100100" := by
  decide

@[simp] theorem suffix14_10100100100100_7 : suffixFrom "10100100100100" 7 = "0100100" := by
  decide

@[simp] theorem suffix14_10100100100100_8 : suffixFrom "10100100100100" 8 = "100100" := by
  decide

@[simp] theorem suffix14_10100100100100_9 : suffixFrom "10100100100100" 9 = "00100" := by
  decide

@[simp] theorem suffix14_10100100100100_10 : suffixFrom "10100100100100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_10100100100100_11 : suffixFrom "10100100100100" 11 = "100" := by
  decide

@[simp] theorem suffix14_10100100100100_12 : suffixFrom "10100100100100" 12 = "00" := by
  decide

@[simp] theorem prefix14_10100100100101_1 : prefixOf "10100100100101" 1 = "1" := by
  decide

@[simp] theorem prefix14_10100100100101_2 : prefixOf "10100100100101" 2 = "10" := by
  decide

@[simp] theorem prefix14_10100100100101_3 : prefixOf "10100100100101" 3 = "101" := by
  decide

@[simp] theorem prefix14_10100100100101_5 : prefixOf "10100100100101" 5 = "10100" := by
  decide

@[simp] theorem prefix14_10100100100101_6 : prefixOf "10100100100101" 6 = "101001" := by
  decide

@[simp] theorem prefix14_10100100100101_7 : prefixOf "10100100100101" 7 = "1010010" := by
  decide

@[simp] theorem prefix14_10100100100101_8 : prefixOf "10100100100101" 8 = "10100100" := by
  decide

@[simp] theorem prefix14_10100100100101_9 : prefixOf "10100100100101" 9 = "101001001" := by
  decide

@[simp] theorem prefix14_10100100100101_10 : prefixOf "10100100100101" 10 = "1010010010" := by
  decide

@[simp] theorem prefix14_10100100100101_11 : prefixOf "10100100100101" 11 = "10100100100" := by
  decide

@[simp] theorem prefix14_10100100100101_12 : prefixOf "10100100100101" 12 = "101001001001" := by
  decide

@[simp] theorem prefix14_10100100100101_13 : prefixOf "10100100100101" 13 = "1010010010010" := by
  decide

@[simp] theorem prefix14_10100100100101_14 : prefixOf "10100100100101" 14 = "10100100100101" := by
  decide

@[simp] theorem suffix14_10100100100101_7 : suffixFrom "10100100100101" 7 = "0100101" := by
  decide

@[simp] theorem suffix14_10100100100101_8 : suffixFrom "10100100100101" 8 = "100101" := by
  decide

@[simp] theorem suffix14_10100100100101_9 : suffixFrom "10100100100101" 9 = "00101" := by
  decide

@[simp] theorem suffix14_10100100100101_10 : suffixFrom "10100100100101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_10100100100101_11 : suffixFrom "10100100100101" 11 = "101" := by
  decide

@[simp] theorem suffix14_10100100100101_12 : suffixFrom "10100100100101" 12 = "01" := by
  decide

@[simp] theorem prefix14_10100100101001_1 : prefixOf "10100100101001" 1 = "1" := by
  decide

@[simp] theorem prefix14_10100100101001_2 : prefixOf "10100100101001" 2 = "10" := by
  decide

@[simp] theorem prefix14_10100100101001_3 : prefixOf "10100100101001" 3 = "101" := by
  decide

@[simp] theorem prefix14_10100100101001_5 : prefixOf "10100100101001" 5 = "10100" := by
  decide

@[simp] theorem prefix14_10100100101001_6 : prefixOf "10100100101001" 6 = "101001" := by
  decide

@[simp] theorem prefix14_10100100101001_7 : prefixOf "10100100101001" 7 = "1010010" := by
  decide

@[simp] theorem prefix14_10100100101001_8 : prefixOf "10100100101001" 8 = "10100100" := by
  decide

@[simp] theorem prefix14_10100100101001_9 : prefixOf "10100100101001" 9 = "101001001" := by
  decide

@[simp] theorem prefix14_10100100101001_10 : prefixOf "10100100101001" 10 = "1010010010" := by
  decide

@[simp] theorem prefix14_10100100101001_11 : prefixOf "10100100101001" 11 = "10100100101" := by
  decide

@[simp] theorem prefix14_10100100101001_12 : prefixOf "10100100101001" 12 = "101001001010" := by
  decide

@[simp] theorem prefix14_10100100101001_13 : prefixOf "10100100101001" 13 = "1010010010100" := by
  decide

@[simp] theorem prefix14_10100100101001_14 : prefixOf "10100100101001" 14 = "10100100101001" := by
  decide

@[simp] theorem suffix14_10100100101001_7 : suffixFrom "10100100101001" 7 = "0101001" := by
  decide

@[simp] theorem suffix14_10100100101001_8 : suffixFrom "10100100101001" 8 = "101001" := by
  decide

@[simp] theorem suffix14_10100100101001_9 : suffixFrom "10100100101001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_10100100101001_10 : suffixFrom "10100100101001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_10100100101001_11 : suffixFrom "10100100101001" 11 = "001" := by
  decide

@[simp] theorem suffix14_10100100101001_12 : suffixFrom "10100100101001" 12 = "01" := by
  decide

@[simp] theorem prefix14_10100100101010_1 : prefixOf "10100100101010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10100100101010_2 : prefixOf "10100100101010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10100100101010_3 : prefixOf "10100100101010" 3 = "101" := by
  decide

@[simp] theorem prefix14_10100100101010_5 : prefixOf "10100100101010" 5 = "10100" := by
  decide

@[simp] theorem prefix14_10100100101010_6 : prefixOf "10100100101010" 6 = "101001" := by
  decide

@[simp] theorem prefix14_10100100101010_7 : prefixOf "10100100101010" 7 = "1010010" := by
  decide

@[simp] theorem prefix14_10100100101010_8 : prefixOf "10100100101010" 8 = "10100100" := by
  decide

@[simp] theorem prefix14_10100100101010_9 : prefixOf "10100100101010" 9 = "101001001" := by
  decide

@[simp] theorem prefix14_10100100101010_10 : prefixOf "10100100101010" 10 = "1010010010" := by
  decide

@[simp] theorem prefix14_10100100101010_11 : prefixOf "10100100101010" 11 = "10100100101" := by
  decide

@[simp] theorem prefix14_10100100101010_12 : prefixOf "10100100101010" 12 = "101001001010" := by
  decide

@[simp] theorem prefix14_10100100101010_13 : prefixOf "10100100101010" 13 = "1010010010101" := by
  decide

@[simp] theorem prefix14_10100100101010_14 : prefixOf "10100100101010" 14 = "10100100101010" := by
  decide

@[simp] theorem suffix14_10100100101010_7 : suffixFrom "10100100101010" 7 = "0101010" := by
  decide

@[simp] theorem suffix14_10100100101010_8 : suffixFrom "10100100101010" 8 = "101010" := by
  decide

@[simp] theorem suffix14_10100100101010_9 : suffixFrom "10100100101010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_10100100101010_10 : suffixFrom "10100100101010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_10100100101010_11 : suffixFrom "10100100101010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10100100101010_12 : suffixFrom "10100100101010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10100101001001_1 : prefixOf "10100101001001" 1 = "1" := by
  decide

@[simp] theorem prefix14_10100101001001_2 : prefixOf "10100101001001" 2 = "10" := by
  decide

@[simp] theorem prefix14_10100101001001_3 : prefixOf "10100101001001" 3 = "101" := by
  decide

@[simp] theorem prefix14_10100101001001_5 : prefixOf "10100101001001" 5 = "10100" := by
  decide

@[simp] theorem prefix14_10100101001001_6 : prefixOf "10100101001001" 6 = "101001" := by
  decide

@[simp] theorem prefix14_10100101001001_7 : prefixOf "10100101001001" 7 = "1010010" := by
  decide

@[simp] theorem prefix14_10100101001001_8 : prefixOf "10100101001001" 8 = "10100101" := by
  decide

@[simp] theorem prefix14_10100101001001_9 : prefixOf "10100101001001" 9 = "101001010" := by
  decide

@[simp] theorem prefix14_10100101001001_10 : prefixOf "10100101001001" 10 = "1010010100" := by
  decide

@[simp] theorem prefix14_10100101001001_11 : prefixOf "10100101001001" 11 = "10100101001" := by
  decide

@[simp] theorem prefix14_10100101001001_12 : prefixOf "10100101001001" 12 = "101001010010" := by
  decide

@[simp] theorem prefix14_10100101001001_13 : prefixOf "10100101001001" 13 = "1010010100100" := by
  decide

@[simp] theorem prefix14_10100101001001_14 : prefixOf "10100101001001" 14 = "10100101001001" := by
  decide

@[simp] theorem suffix14_10100101001001_7 : suffixFrom "10100101001001" 7 = "1001001" := by
  decide

@[simp] theorem suffix14_10100101001001_8 : suffixFrom "10100101001001" 8 = "001001" := by
  decide

@[simp] theorem suffix14_10100101001001_9 : suffixFrom "10100101001001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_10100101001001_10 : suffixFrom "10100101001001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_10100101001001_11 : suffixFrom "10100101001001" 11 = "001" := by
  decide

@[simp] theorem suffix14_10100101001001_12 : suffixFrom "10100101001001" 12 = "01" := by
  decide

@[simp] theorem prefix14_10100101001010_1 : prefixOf "10100101001010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10100101001010_2 : prefixOf "10100101001010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10100101001010_3 : prefixOf "10100101001010" 3 = "101" := by
  decide

@[simp] theorem prefix14_10100101001010_5 : prefixOf "10100101001010" 5 = "10100" := by
  decide

@[simp] theorem prefix14_10100101001010_6 : prefixOf "10100101001010" 6 = "101001" := by
  decide

@[simp] theorem prefix14_10100101001010_7 : prefixOf "10100101001010" 7 = "1010010" := by
  decide

@[simp] theorem prefix14_10100101001010_8 : prefixOf "10100101001010" 8 = "10100101" := by
  decide

@[simp] theorem prefix14_10100101001010_9 : prefixOf "10100101001010" 9 = "101001010" := by
  decide

@[simp] theorem prefix14_10100101001010_10 : prefixOf "10100101001010" 10 = "1010010100" := by
  decide

@[simp] theorem prefix14_10100101001010_11 : prefixOf "10100101001010" 11 = "10100101001" := by
  decide

@[simp] theorem prefix14_10100101001010_12 : prefixOf "10100101001010" 12 = "101001010010" := by
  decide

@[simp] theorem prefix14_10100101001010_13 : prefixOf "10100101001010" 13 = "1010010100101" := by
  decide

@[simp] theorem prefix14_10100101001010_14 : prefixOf "10100101001010" 14 = "10100101001010" := by
  decide

@[simp] theorem suffix14_10100101001010_7 : suffixFrom "10100101001010" 7 = "1001010" := by
  decide

@[simp] theorem suffix14_10100101001010_8 : suffixFrom "10100101001010" 8 = "001010" := by
  decide

@[simp] theorem suffix14_10100101001010_9 : suffixFrom "10100101001010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_10100101001010_10 : suffixFrom "10100101001010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_10100101001010_11 : suffixFrom "10100101001010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10100101001010_12 : suffixFrom "10100101001010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10100101010010_1 : prefixOf "10100101010010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10100101010010_2 : prefixOf "10100101010010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10100101010010_3 : prefixOf "10100101010010" 3 = "101" := by
  decide

@[simp] theorem prefix14_10100101010010_5 : prefixOf "10100101010010" 5 = "10100" := by
  decide

@[simp] theorem prefix14_10100101010010_6 : prefixOf "10100101010010" 6 = "101001" := by
  decide

@[simp] theorem prefix14_10100101010010_7 : prefixOf "10100101010010" 7 = "1010010" := by
  decide

@[simp] theorem prefix14_10100101010010_8 : prefixOf "10100101010010" 8 = "10100101" := by
  decide

@[simp] theorem prefix14_10100101010010_9 : prefixOf "10100101010010" 9 = "101001010" := by
  decide

@[simp] theorem prefix14_10100101010010_10 : prefixOf "10100101010010" 10 = "1010010101" := by
  decide

@[simp] theorem prefix14_10100101010010_11 : prefixOf "10100101010010" 11 = "10100101010" := by
  decide

@[simp] theorem prefix14_10100101010010_12 : prefixOf "10100101010010" 12 = "101001010100" := by
  decide

@[simp] theorem prefix14_10100101010010_13 : prefixOf "10100101010010" 13 = "1010010101001" := by
  decide

@[simp] theorem prefix14_10100101010010_14 : prefixOf "10100101010010" 14 = "10100101010010" := by
  decide

@[simp] theorem suffix14_10100101010010_7 : suffixFrom "10100101010010" 7 = "1010010" := by
  decide

@[simp] theorem suffix14_10100101010010_8 : suffixFrom "10100101010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_10100101010010_9 : suffixFrom "10100101010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_10100101010010_10 : suffixFrom "10100101010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_10100101010010_11 : suffixFrom "10100101010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10100101010010_12 : suffixFrom "10100101010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10100101010100_1 : prefixOf "10100101010100" 1 = "1" := by
  decide

@[simp] theorem prefix14_10100101010100_2 : prefixOf "10100101010100" 2 = "10" := by
  decide

@[simp] theorem prefix14_10100101010100_3 : prefixOf "10100101010100" 3 = "101" := by
  decide

@[simp] theorem prefix14_10100101010100_5 : prefixOf "10100101010100" 5 = "10100" := by
  decide

@[simp] theorem prefix14_10100101010100_6 : prefixOf "10100101010100" 6 = "101001" := by
  decide

@[simp] theorem prefix14_10100101010100_7 : prefixOf "10100101010100" 7 = "1010010" := by
  decide

@[simp] theorem prefix14_10100101010100_8 : prefixOf "10100101010100" 8 = "10100101" := by
  decide

@[simp] theorem prefix14_10100101010100_9 : prefixOf "10100101010100" 9 = "101001010" := by
  decide

@[simp] theorem prefix14_10100101010100_10 : prefixOf "10100101010100" 10 = "1010010101" := by
  decide

@[simp] theorem prefix14_10100101010100_11 : prefixOf "10100101010100" 11 = "10100101010" := by
  decide

@[simp] theorem prefix14_10100101010100_12 : prefixOf "10100101010100" 12 = "101001010101" := by
  decide

@[simp] theorem prefix14_10100101010100_13 : prefixOf "10100101010100" 13 = "1010010101010" := by
  decide

@[simp] theorem prefix14_10100101010100_14 : prefixOf "10100101010100" 14 = "10100101010100" := by
  decide

@[simp] theorem suffix14_10100101010100_7 : suffixFrom "10100101010100" 7 = "1010100" := by
  decide

@[simp] theorem suffix14_10100101010100_8 : suffixFrom "10100101010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_10100101010100_9 : suffixFrom "10100101010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_10100101010100_10 : suffixFrom "10100101010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_10100101010100_11 : suffixFrom "10100101010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_10100101010100_12 : suffixFrom "10100101010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_10100101010101_1 : prefixOf "10100101010101" 1 = "1" := by
  decide

@[simp] theorem prefix14_10100101010101_2 : prefixOf "10100101010101" 2 = "10" := by
  decide

@[simp] theorem prefix14_10100101010101_3 : prefixOf "10100101010101" 3 = "101" := by
  decide

@[simp] theorem prefix14_10100101010101_5 : prefixOf "10100101010101" 5 = "10100" := by
  decide

@[simp] theorem prefix14_10100101010101_6 : prefixOf "10100101010101" 6 = "101001" := by
  decide

@[simp] theorem prefix14_10100101010101_7 : prefixOf "10100101010101" 7 = "1010010" := by
  decide

@[simp] theorem prefix14_10100101010101_8 : prefixOf "10100101010101" 8 = "10100101" := by
  decide

@[simp] theorem prefix14_10100101010101_9 : prefixOf "10100101010101" 9 = "101001010" := by
  decide

@[simp] theorem prefix14_10100101010101_10 : prefixOf "10100101010101" 10 = "1010010101" := by
  decide

@[simp] theorem prefix14_10100101010101_11 : prefixOf "10100101010101" 11 = "10100101010" := by
  decide

@[simp] theorem prefix14_10100101010101_12 : prefixOf "10100101010101" 12 = "101001010101" := by
  decide

@[simp] theorem prefix14_10100101010101_13 : prefixOf "10100101010101" 13 = "1010010101010" := by
  decide

@[simp] theorem prefix14_10100101010101_14 : prefixOf "10100101010101" 14 = "10100101010101" := by
  decide

@[simp] theorem suffix14_10100101010101_7 : suffixFrom "10100101010101" 7 = "1010101" := by
  decide

@[simp] theorem suffix14_10100101010101_8 : suffixFrom "10100101010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_10100101010101_9 : suffixFrom "10100101010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_10100101010101_10 : suffixFrom "10100101010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_10100101010101_11 : suffixFrom "10100101010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_10100101010101_12 : suffixFrom "10100101010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_10101001001001_1 : prefixOf "10101001001001" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101001001001_2 : prefixOf "10101001001001" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101001001001_3 : prefixOf "10101001001001" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101001001001_5 : prefixOf "10101001001001" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101001001001_6 : prefixOf "10101001001001" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101001001001_7 : prefixOf "10101001001001" 7 = "1010100" := by
  decide

@[simp] theorem prefix14_10101001001001_8 : prefixOf "10101001001001" 8 = "10101001" := by
  decide

@[simp] theorem prefix14_10101001001001_9 : prefixOf "10101001001001" 9 = "101010010" := by
  decide

@[simp] theorem prefix14_10101001001001_10 : prefixOf "10101001001001" 10 = "1010100100" := by
  decide

@[simp] theorem prefix14_10101001001001_11 : prefixOf "10101001001001" 11 = "10101001001" := by
  decide

@[simp] theorem prefix14_10101001001001_12 : prefixOf "10101001001001" 12 = "101010010010" := by
  decide

@[simp] theorem prefix14_10101001001001_13 : prefixOf "10101001001001" 13 = "1010100100100" := by
  decide

@[simp] theorem prefix14_10101001001001_14 : prefixOf "10101001001001" 14 = "10101001001001" := by
  decide

@[simp] theorem suffix14_10101001001001_7 : suffixFrom "10101001001001" 7 = "1001001" := by
  decide

@[simp] theorem suffix14_10101001001001_8 : suffixFrom "10101001001001" 8 = "001001" := by
  decide

@[simp] theorem suffix14_10101001001001_9 : suffixFrom "10101001001001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_10101001001001_10 : suffixFrom "10101001001001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_10101001001001_11 : suffixFrom "10101001001001" 11 = "001" := by
  decide

@[simp] theorem suffix14_10101001001001_12 : suffixFrom "10101001001001" 12 = "01" := by
  decide

@[simp] theorem prefix14_10101001001010_1 : prefixOf "10101001001010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101001001010_2 : prefixOf "10101001001010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101001001010_3 : prefixOf "10101001001010" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101001001010_5 : prefixOf "10101001001010" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101001001010_6 : prefixOf "10101001001010" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101001001010_7 : prefixOf "10101001001010" 7 = "1010100" := by
  decide

@[simp] theorem prefix14_10101001001010_8 : prefixOf "10101001001010" 8 = "10101001" := by
  decide

@[simp] theorem prefix14_10101001001010_9 : prefixOf "10101001001010" 9 = "101010010" := by
  decide

@[simp] theorem prefix14_10101001001010_10 : prefixOf "10101001001010" 10 = "1010100100" := by
  decide

@[simp] theorem prefix14_10101001001010_11 : prefixOf "10101001001010" 11 = "10101001001" := by
  decide

@[simp] theorem prefix14_10101001001010_12 : prefixOf "10101001001010" 12 = "101010010010" := by
  decide

@[simp] theorem prefix14_10101001001010_13 : prefixOf "10101001001010" 13 = "1010100100101" := by
  decide

@[simp] theorem prefix14_10101001001010_14 : prefixOf "10101001001010" 14 = "10101001001010" := by
  decide

@[simp] theorem suffix14_10101001001010_7 : suffixFrom "10101001001010" 7 = "1001010" := by
  decide

@[simp] theorem suffix14_10101001001010_8 : suffixFrom "10101001001010" 8 = "001010" := by
  decide

@[simp] theorem suffix14_10101001001010_9 : suffixFrom "10101001001010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_10101001001010_10 : suffixFrom "10101001001010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_10101001001010_11 : suffixFrom "10101001001010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10101001001010_12 : suffixFrom "10101001001010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10101001010010_1 : prefixOf "10101001010010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101001010010_2 : prefixOf "10101001010010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101001010010_3 : prefixOf "10101001010010" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101001010010_5 : prefixOf "10101001010010" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101001010010_6 : prefixOf "10101001010010" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101001010010_7 : prefixOf "10101001010010" 7 = "1010100" := by
  decide

@[simp] theorem prefix14_10101001010010_8 : prefixOf "10101001010010" 8 = "10101001" := by
  decide

@[simp] theorem prefix14_10101001010010_9 : prefixOf "10101001010010" 9 = "101010010" := by
  decide

@[simp] theorem prefix14_10101001010010_10 : prefixOf "10101001010010" 10 = "1010100101" := by
  decide

@[simp] theorem prefix14_10101001010010_11 : prefixOf "10101001010010" 11 = "10101001010" := by
  decide

@[simp] theorem prefix14_10101001010010_12 : prefixOf "10101001010010" 12 = "101010010100" := by
  decide

@[simp] theorem prefix14_10101001010010_13 : prefixOf "10101001010010" 13 = "1010100101001" := by
  decide

@[simp] theorem prefix14_10101001010010_14 : prefixOf "10101001010010" 14 = "10101001010010" := by
  decide

@[simp] theorem suffix14_10101001010010_7 : suffixFrom "10101001010010" 7 = "1010010" := by
  decide

@[simp] theorem suffix14_10101001010010_8 : suffixFrom "10101001010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_10101001010010_9 : suffixFrom "10101001010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_10101001010010_10 : suffixFrom "10101001010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_10101001010010_11 : suffixFrom "10101001010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10101001010010_12 : suffixFrom "10101001010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10101001010100_1 : prefixOf "10101001010100" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101001010100_2 : prefixOf "10101001010100" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101001010100_3 : prefixOf "10101001010100" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101001010100_5 : prefixOf "10101001010100" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101001010100_6 : prefixOf "10101001010100" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101001010100_7 : prefixOf "10101001010100" 7 = "1010100" := by
  decide

@[simp] theorem prefix14_10101001010100_8 : prefixOf "10101001010100" 8 = "10101001" := by
  decide

@[simp] theorem prefix14_10101001010100_9 : prefixOf "10101001010100" 9 = "101010010" := by
  decide

@[simp] theorem prefix14_10101001010100_10 : prefixOf "10101001010100" 10 = "1010100101" := by
  decide

@[simp] theorem prefix14_10101001010100_11 : prefixOf "10101001010100" 11 = "10101001010" := by
  decide

@[simp] theorem prefix14_10101001010100_12 : prefixOf "10101001010100" 12 = "101010010101" := by
  decide

@[simp] theorem prefix14_10101001010100_13 : prefixOf "10101001010100" 13 = "1010100101010" := by
  decide

@[simp] theorem prefix14_10101001010100_14 : prefixOf "10101001010100" 14 = "10101001010100" := by
  decide

@[simp] theorem suffix14_10101001010100_7 : suffixFrom "10101001010100" 7 = "1010100" := by
  decide

@[simp] theorem suffix14_10101001010100_8 : suffixFrom "10101001010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_10101001010100_9 : suffixFrom "10101001010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_10101001010100_10 : suffixFrom "10101001010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_10101001010100_11 : suffixFrom "10101001010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_10101001010100_12 : suffixFrom "10101001010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_10101001010101_1 : prefixOf "10101001010101" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101001010101_2 : prefixOf "10101001010101" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101001010101_3 : prefixOf "10101001010101" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101001010101_5 : prefixOf "10101001010101" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101001010101_6 : prefixOf "10101001010101" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101001010101_7 : prefixOf "10101001010101" 7 = "1010100" := by
  decide

@[simp] theorem prefix14_10101001010101_8 : prefixOf "10101001010101" 8 = "10101001" := by
  decide

@[simp] theorem prefix14_10101001010101_9 : prefixOf "10101001010101" 9 = "101010010" := by
  decide

@[simp] theorem prefix14_10101001010101_10 : prefixOf "10101001010101" 10 = "1010100101" := by
  decide

@[simp] theorem prefix14_10101001010101_11 : prefixOf "10101001010101" 11 = "10101001010" := by
  decide

@[simp] theorem prefix14_10101001010101_12 : prefixOf "10101001010101" 12 = "101010010101" := by
  decide

@[simp] theorem prefix14_10101001010101_13 : prefixOf "10101001010101" 13 = "1010100101010" := by
  decide

@[simp] theorem prefix14_10101001010101_14 : prefixOf "10101001010101" 14 = "10101001010101" := by
  decide

@[simp] theorem suffix14_10101001010101_7 : suffixFrom "10101001010101" 7 = "1010101" := by
  decide

@[simp] theorem suffix14_10101001010101_8 : suffixFrom "10101001010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_10101001010101_9 : suffixFrom "10101001010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_10101001010101_10 : suffixFrom "10101001010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_10101001010101_11 : suffixFrom "10101001010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_10101001010101_12 : suffixFrom "10101001010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_10101010010010_1 : prefixOf "10101010010010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101010010010_2 : prefixOf "10101010010010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101010010010_3 : prefixOf "10101010010010" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101010010010_5 : prefixOf "10101010010010" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101010010010_6 : prefixOf "10101010010010" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101010010010_7 : prefixOf "10101010010010" 7 = "1010101" := by
  decide

@[simp] theorem prefix14_10101010010010_8 : prefixOf "10101010010010" 8 = "10101010" := by
  decide

@[simp] theorem prefix14_10101010010010_9 : prefixOf "10101010010010" 9 = "101010100" := by
  decide

@[simp] theorem prefix14_10101010010010_10 : prefixOf "10101010010010" 10 = "1010101001" := by
  decide

@[simp] theorem prefix14_10101010010010_11 : prefixOf "10101010010010" 11 = "10101010010" := by
  decide

@[simp] theorem prefix14_10101010010010_12 : prefixOf "10101010010010" 12 = "101010100100" := by
  decide

@[simp] theorem prefix14_10101010010010_13 : prefixOf "10101010010010" 13 = "1010101001001" := by
  decide

@[simp] theorem prefix14_10101010010010_14 : prefixOf "10101010010010" 14 = "10101010010010" := by
  decide

@[simp] theorem suffix14_10101010010010_7 : suffixFrom "10101010010010" 7 = "0010010" := by
  decide

@[simp] theorem suffix14_10101010010010_8 : suffixFrom "10101010010010" 8 = "010010" := by
  decide

@[simp] theorem suffix14_10101010010010_9 : suffixFrom "10101010010010" 9 = "10010" := by
  decide

@[simp] theorem suffix14_10101010010010_10 : suffixFrom "10101010010010" 10 = "0010" := by
  decide

@[simp] theorem suffix14_10101010010010_11 : suffixFrom "10101010010010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10101010010010_12 : suffixFrom "10101010010010" 12 = "10" := by
  decide

@[simp] theorem prefix14_10101010010100_1 : prefixOf "10101010010100" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101010010100_2 : prefixOf "10101010010100" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101010010100_3 : prefixOf "10101010010100" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101010010100_5 : prefixOf "10101010010100" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101010010100_6 : prefixOf "10101010010100" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101010010100_7 : prefixOf "10101010010100" 7 = "1010101" := by
  decide

@[simp] theorem prefix14_10101010010100_8 : prefixOf "10101010010100" 8 = "10101010" := by
  decide

@[simp] theorem prefix14_10101010010100_9 : prefixOf "10101010010100" 9 = "101010100" := by
  decide

@[simp] theorem prefix14_10101010010100_10 : prefixOf "10101010010100" 10 = "1010101001" := by
  decide

@[simp] theorem prefix14_10101010010100_11 : prefixOf "10101010010100" 11 = "10101010010" := by
  decide

@[simp] theorem prefix14_10101010010100_12 : prefixOf "10101010010100" 12 = "101010100101" := by
  decide

@[simp] theorem prefix14_10101010010100_13 : prefixOf "10101010010100" 13 = "1010101001010" := by
  decide

@[simp] theorem prefix14_10101010010100_14 : prefixOf "10101010010100" 14 = "10101010010100" := by
  decide

@[simp] theorem suffix14_10101010010100_7 : suffixFrom "10101010010100" 7 = "0010100" := by
  decide

@[simp] theorem suffix14_10101010010100_8 : suffixFrom "10101010010100" 8 = "010100" := by
  decide

@[simp] theorem suffix14_10101010010100_9 : suffixFrom "10101010010100" 9 = "10100" := by
  decide

@[simp] theorem suffix14_10101010010100_10 : suffixFrom "10101010010100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_10101010010100_11 : suffixFrom "10101010010100" 11 = "100" := by
  decide

@[simp] theorem suffix14_10101010010100_12 : suffixFrom "10101010010100" 12 = "00" := by
  decide

@[simp] theorem prefix14_10101010010101_1 : prefixOf "10101010010101" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101010010101_2 : prefixOf "10101010010101" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101010010101_3 : prefixOf "10101010010101" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101010010101_5 : prefixOf "10101010010101" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101010010101_6 : prefixOf "10101010010101" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101010010101_7 : prefixOf "10101010010101" 7 = "1010101" := by
  decide

@[simp] theorem prefix14_10101010010101_8 : prefixOf "10101010010101" 8 = "10101010" := by
  decide

@[simp] theorem prefix14_10101010010101_9 : prefixOf "10101010010101" 9 = "101010100" := by
  decide

@[simp] theorem prefix14_10101010010101_10 : prefixOf "10101010010101" 10 = "1010101001" := by
  decide

@[simp] theorem prefix14_10101010010101_11 : prefixOf "10101010010101" 11 = "10101010010" := by
  decide

@[simp] theorem prefix14_10101010010101_12 : prefixOf "10101010010101" 12 = "101010100101" := by
  decide

@[simp] theorem prefix14_10101010010101_13 : prefixOf "10101010010101" 13 = "1010101001010" := by
  decide

@[simp] theorem prefix14_10101010010101_14 : prefixOf "10101010010101" 14 = "10101010010101" := by
  decide

@[simp] theorem suffix14_10101010010101_7 : suffixFrom "10101010010101" 7 = "0010101" := by
  decide

@[simp] theorem suffix14_10101010010101_8 : suffixFrom "10101010010101" 8 = "010101" := by
  decide

@[simp] theorem suffix14_10101010010101_9 : suffixFrom "10101010010101" 9 = "10101" := by
  decide

@[simp] theorem suffix14_10101010010101_10 : suffixFrom "10101010010101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_10101010010101_11 : suffixFrom "10101010010101" 11 = "101" := by
  decide

@[simp] theorem suffix14_10101010010101_12 : suffixFrom "10101010010101" 12 = "01" := by
  decide

@[simp] theorem prefix14_10101010100100_1 : prefixOf "10101010100100" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101010100100_2 : prefixOf "10101010100100" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101010100100_3 : prefixOf "10101010100100" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101010100100_5 : prefixOf "10101010100100" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101010100100_6 : prefixOf "10101010100100" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101010100100_7 : prefixOf "10101010100100" 7 = "1010101" := by
  decide

@[simp] theorem prefix14_10101010100100_8 : prefixOf "10101010100100" 8 = "10101010" := by
  decide

@[simp] theorem prefix14_10101010100100_9 : prefixOf "10101010100100" 9 = "101010101" := by
  decide

@[simp] theorem prefix14_10101010100100_10 : prefixOf "10101010100100" 10 = "1010101010" := by
  decide

@[simp] theorem prefix14_10101010100100_11 : prefixOf "10101010100100" 11 = "10101010100" := by
  decide

@[simp] theorem prefix14_10101010100100_12 : prefixOf "10101010100100" 12 = "101010101001" := by
  decide

@[simp] theorem prefix14_10101010100100_13 : prefixOf "10101010100100" 13 = "1010101010010" := by
  decide

@[simp] theorem prefix14_10101010100100_14 : prefixOf "10101010100100" 14 = "10101010100100" := by
  decide

@[simp] theorem suffix14_10101010100100_7 : suffixFrom "10101010100100" 7 = "0100100" := by
  decide

@[simp] theorem suffix14_10101010100100_8 : suffixFrom "10101010100100" 8 = "100100" := by
  decide

@[simp] theorem suffix14_10101010100100_9 : suffixFrom "10101010100100" 9 = "00100" := by
  decide

@[simp] theorem suffix14_10101010100100_10 : suffixFrom "10101010100100" 10 = "0100" := by
  decide

@[simp] theorem suffix14_10101010100100_11 : suffixFrom "10101010100100" 11 = "100" := by
  decide

@[simp] theorem suffix14_10101010100100_12 : suffixFrom "10101010100100" 12 = "00" := by
  decide

@[simp] theorem prefix14_10101010100101_1 : prefixOf "10101010100101" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101010100101_2 : prefixOf "10101010100101" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101010100101_3 : prefixOf "10101010100101" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101010100101_5 : prefixOf "10101010100101" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101010100101_6 : prefixOf "10101010100101" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101010100101_7 : prefixOf "10101010100101" 7 = "1010101" := by
  decide

@[simp] theorem prefix14_10101010100101_8 : prefixOf "10101010100101" 8 = "10101010" := by
  decide

@[simp] theorem prefix14_10101010100101_9 : prefixOf "10101010100101" 9 = "101010101" := by
  decide

@[simp] theorem prefix14_10101010100101_10 : prefixOf "10101010100101" 10 = "1010101010" := by
  decide

@[simp] theorem prefix14_10101010100101_11 : prefixOf "10101010100101" 11 = "10101010100" := by
  decide

@[simp] theorem prefix14_10101010100101_12 : prefixOf "10101010100101" 12 = "101010101001" := by
  decide

@[simp] theorem prefix14_10101010100101_13 : prefixOf "10101010100101" 13 = "1010101010010" := by
  decide

@[simp] theorem prefix14_10101010100101_14 : prefixOf "10101010100101" 14 = "10101010100101" := by
  decide

@[simp] theorem suffix14_10101010100101_7 : suffixFrom "10101010100101" 7 = "0100101" := by
  decide

@[simp] theorem suffix14_10101010100101_8 : suffixFrom "10101010100101" 8 = "100101" := by
  decide

@[simp] theorem suffix14_10101010100101_9 : suffixFrom "10101010100101" 9 = "00101" := by
  decide

@[simp] theorem suffix14_10101010100101_10 : suffixFrom "10101010100101" 10 = "0101" := by
  decide

@[simp] theorem suffix14_10101010100101_11 : suffixFrom "10101010100101" 11 = "101" := by
  decide

@[simp] theorem suffix14_10101010100101_12 : suffixFrom "10101010100101" 12 = "01" := by
  decide

@[simp] theorem prefix14_10101010101001_1 : prefixOf "10101010101001" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101010101001_2 : prefixOf "10101010101001" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101010101001_3 : prefixOf "10101010101001" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101010101001_5 : prefixOf "10101010101001" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101010101001_6 : prefixOf "10101010101001" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101010101001_7 : prefixOf "10101010101001" 7 = "1010101" := by
  decide

@[simp] theorem prefix14_10101010101001_8 : prefixOf "10101010101001" 8 = "10101010" := by
  decide

@[simp] theorem prefix14_10101010101001_9 : prefixOf "10101010101001" 9 = "101010101" := by
  decide

@[simp] theorem prefix14_10101010101001_10 : prefixOf "10101010101001" 10 = "1010101010" := by
  decide

@[simp] theorem prefix14_10101010101001_11 : prefixOf "10101010101001" 11 = "10101010101" := by
  decide

@[simp] theorem prefix14_10101010101001_12 : prefixOf "10101010101001" 12 = "101010101010" := by
  decide

@[simp] theorem prefix14_10101010101001_13 : prefixOf "10101010101001" 13 = "1010101010100" := by
  decide

@[simp] theorem prefix14_10101010101001_14 : prefixOf "10101010101001" 14 = "10101010101001" := by
  decide

@[simp] theorem suffix14_10101010101001_7 : suffixFrom "10101010101001" 7 = "0101001" := by
  decide

@[simp] theorem suffix14_10101010101001_8 : suffixFrom "10101010101001" 8 = "101001" := by
  decide

@[simp] theorem suffix14_10101010101001_9 : suffixFrom "10101010101001" 9 = "01001" := by
  decide

@[simp] theorem suffix14_10101010101001_10 : suffixFrom "10101010101001" 10 = "1001" := by
  decide

@[simp] theorem suffix14_10101010101001_11 : suffixFrom "10101010101001" 11 = "001" := by
  decide

@[simp] theorem suffix14_10101010101001_12 : suffixFrom "10101010101001" 12 = "01" := by
  decide

@[simp] theorem prefix14_10101010101010_1 : prefixOf "10101010101010" 1 = "1" := by
  decide

@[simp] theorem prefix14_10101010101010_2 : prefixOf "10101010101010" 2 = "10" := by
  decide

@[simp] theorem prefix14_10101010101010_3 : prefixOf "10101010101010" 3 = "101" := by
  decide

@[simp] theorem prefix14_10101010101010_5 : prefixOf "10101010101010" 5 = "10101" := by
  decide

@[simp] theorem prefix14_10101010101010_6 : prefixOf "10101010101010" 6 = "101010" := by
  decide

@[simp] theorem prefix14_10101010101010_7 : prefixOf "10101010101010" 7 = "1010101" := by
  decide

@[simp] theorem prefix14_10101010101010_8 : prefixOf "10101010101010" 8 = "10101010" := by
  decide

@[simp] theorem prefix14_10101010101010_9 : prefixOf "10101010101010" 9 = "101010101" := by
  decide

@[simp] theorem prefix14_10101010101010_10 : prefixOf "10101010101010" 10 = "1010101010" := by
  decide

@[simp] theorem prefix14_10101010101010_11 : prefixOf "10101010101010" 11 = "10101010101" := by
  decide

@[simp] theorem prefix14_10101010101010_12 : prefixOf "10101010101010" 12 = "101010101010" := by
  decide

@[simp] theorem prefix14_10101010101010_13 : prefixOf "10101010101010" 13 = "1010101010101" := by
  decide

@[simp] theorem prefix14_10101010101010_14 : prefixOf "10101010101010" 14 = "10101010101010" := by
  decide

@[simp] theorem suffix14_10101010101010_7 : suffixFrom "10101010101010" 7 = "0101010" := by
  decide

@[simp] theorem suffix14_10101010101010_8 : suffixFrom "10101010101010" 8 = "101010" := by
  decide

@[simp] theorem suffix14_10101010101010_9 : suffixFrom "10101010101010" 9 = "01010" := by
  decide

@[simp] theorem suffix14_10101010101010_10 : suffixFrom "10101010101010" 10 = "1010" := by
  decide

@[simp] theorem suffix14_10101010101010_11 : suffixFrom "10101010101010" 11 = "010" := by
  decide

@[simp] theorem suffix14_10101010101010_12 : suffixFrom "10101010101010" 12 = "10" := by
  decide

@[simp] theorem prefix7_0010010_2 : prefixOf "0010010" 2 = "00" := by
  decide

@[simp] theorem prefix7_0010010_3 : prefixOf "0010010" 3 = "001" := by
  decide

@[simp] theorem prefix7_0010010_4 : prefixOf "0010010" 4 = "0010" := by
  decide

@[simp] theorem prefix7_0010010_5 : prefixOf "0010010" 5 = "00100" := by
  decide

@[simp] theorem prefix7_0010010_6 : prefixOf "0010010" 6 = "001001" := by
  decide

@[simp] theorem prefix7_0010010_7 : prefixOf "0010010" 7 = "0010010" := by
  decide

@[simp] theorem prefix7_0010100_2 : prefixOf "0010100" 2 = "00" := by
  decide

@[simp] theorem prefix7_0010100_3 : prefixOf "0010100" 3 = "001" := by
  decide

@[simp] theorem prefix7_0010100_4 : prefixOf "0010100" 4 = "0010" := by
  decide

@[simp] theorem prefix7_0010100_5 : prefixOf "0010100" 5 = "00101" := by
  decide

@[simp] theorem prefix7_0010100_6 : prefixOf "0010100" 6 = "001010" := by
  decide

@[simp] theorem prefix7_0010100_7 : prefixOf "0010100" 7 = "0010100" := by
  decide

@[simp] theorem prefix7_0010101_2 : prefixOf "0010101" 2 = "00" := by
  decide

@[simp] theorem prefix7_0010101_3 : prefixOf "0010101" 3 = "001" := by
  decide

@[simp] theorem prefix7_0010101_4 : prefixOf "0010101" 4 = "0010" := by
  decide

@[simp] theorem prefix7_0010101_5 : prefixOf "0010101" 5 = "00101" := by
  decide

@[simp] theorem prefix7_0010101_6 : prefixOf "0010101" 6 = "001010" := by
  decide

@[simp] theorem prefix7_0010101_7 : prefixOf "0010101" 7 = "0010101" := by
  decide

@[simp] theorem prefix7_0100100_2 : prefixOf "0100100" 2 = "01" := by
  decide

@[simp] theorem prefix7_0100100_3 : prefixOf "0100100" 3 = "010" := by
  decide

@[simp] theorem prefix7_0100100_4 : prefixOf "0100100" 4 = "0100" := by
  decide

@[simp] theorem prefix7_0100100_5 : prefixOf "0100100" 5 = "01001" := by
  decide

@[simp] theorem prefix7_0100100_6 : prefixOf "0100100" 6 = "010010" := by
  decide

@[simp] theorem prefix7_0100100_7 : prefixOf "0100100" 7 = "0100100" := by
  decide

@[simp] theorem prefix7_0100101_2 : prefixOf "0100101" 2 = "01" := by
  decide

@[simp] theorem prefix7_0100101_3 : prefixOf "0100101" 3 = "010" := by
  decide

@[simp] theorem prefix7_0100101_4 : prefixOf "0100101" 4 = "0100" := by
  decide

@[simp] theorem prefix7_0100101_5 : prefixOf "0100101" 5 = "01001" := by
  decide

@[simp] theorem prefix7_0100101_6 : prefixOf "0100101" 6 = "010010" := by
  decide

@[simp] theorem prefix7_0100101_7 : prefixOf "0100101" 7 = "0100101" := by
  decide

@[simp] theorem prefix7_0101001_2 : prefixOf "0101001" 2 = "01" := by
  decide

@[simp] theorem prefix7_0101001_3 : prefixOf "0101001" 3 = "010" := by
  decide

@[simp] theorem prefix7_0101001_4 : prefixOf "0101001" 4 = "0101" := by
  decide

@[simp] theorem prefix7_0101001_5 : prefixOf "0101001" 5 = "01010" := by
  decide

@[simp] theorem prefix7_0101001_6 : prefixOf "0101001" 6 = "010100" := by
  decide

@[simp] theorem prefix7_0101001_7 : prefixOf "0101001" 7 = "0101001" := by
  decide

@[simp] theorem prefix7_0101010_2 : prefixOf "0101010" 2 = "01" := by
  decide

@[simp] theorem prefix7_0101010_3 : prefixOf "0101010" 3 = "010" := by
  decide

@[simp] theorem prefix7_0101010_4 : prefixOf "0101010" 4 = "0101" := by
  decide

@[simp] theorem prefix7_0101010_5 : prefixOf "0101010" 5 = "01010" := by
  decide

@[simp] theorem prefix7_0101010_6 : prefixOf "0101010" 6 = "010101" := by
  decide

@[simp] theorem prefix7_0101010_7 : prefixOf "0101010" 7 = "0101010" := by
  decide

@[simp] theorem prefix7_1001001_2 : prefixOf "1001001" 2 = "10" := by
  decide

@[simp] theorem prefix7_1001001_3 : prefixOf "1001001" 3 = "100" := by
  decide

@[simp] theorem prefix7_1001001_4 : prefixOf "1001001" 4 = "1001" := by
  decide

@[simp] theorem prefix7_1001001_5 : prefixOf "1001001" 5 = "10010" := by
  decide

@[simp] theorem prefix7_1001001_6 : prefixOf "1001001" 6 = "100100" := by
  decide

@[simp] theorem prefix7_1001001_7 : prefixOf "1001001" 7 = "1001001" := by
  decide

@[simp] theorem prefix7_1001010_2 : prefixOf "1001010" 2 = "10" := by
  decide

@[simp] theorem prefix7_1001010_3 : prefixOf "1001010" 3 = "100" := by
  decide

@[simp] theorem prefix7_1001010_4 : prefixOf "1001010" 4 = "1001" := by
  decide

@[simp] theorem prefix7_1001010_5 : prefixOf "1001010" 5 = "10010" := by
  decide

@[simp] theorem prefix7_1001010_6 : prefixOf "1001010" 6 = "100101" := by
  decide

@[simp] theorem prefix7_1001010_7 : prefixOf "1001010" 7 = "1001010" := by
  decide

@[simp] theorem prefix7_1010010_2 : prefixOf "1010010" 2 = "10" := by
  decide

@[simp] theorem prefix7_1010010_3 : prefixOf "1010010" 3 = "101" := by
  decide

@[simp] theorem prefix7_1010010_4 : prefixOf "1010010" 4 = "1010" := by
  decide

@[simp] theorem prefix7_1010010_5 : prefixOf "1010010" 5 = "10100" := by
  decide

@[simp] theorem prefix7_1010010_6 : prefixOf "1010010" 6 = "101001" := by
  decide

@[simp] theorem prefix7_1010010_7 : prefixOf "1010010" 7 = "1010010" := by
  decide

@[simp] theorem prefix7_1010100_2 : prefixOf "1010100" 2 = "10" := by
  decide

@[simp] theorem prefix7_1010100_3 : prefixOf "1010100" 3 = "101" := by
  decide

@[simp] theorem prefix7_1010100_4 : prefixOf "1010100" 4 = "1010" := by
  decide

@[simp] theorem prefix7_1010100_5 : prefixOf "1010100" 5 = "10101" := by
  decide

@[simp] theorem prefix7_1010100_6 : prefixOf "1010100" 6 = "101010" := by
  decide

@[simp] theorem prefix7_1010100_7 : prefixOf "1010100" 7 = "1010100" := by
  decide

@[simp] theorem prefix7_1010101_2 : prefixOf "1010101" 2 = "10" := by
  decide

@[simp] theorem prefix7_1010101_3 : prefixOf "1010101" 3 = "101" := by
  decide

@[simp] theorem prefix7_1010101_4 : prefixOf "1010101" 4 = "1010" := by
  decide

@[simp] theorem prefix7_1010101_5 : prefixOf "1010101" 5 = "10101" := by
  decide

@[simp] theorem prefix7_1010101_6 : prefixOf "1010101" 6 = "101010" := by
  decide

@[simp] theorem prefix7_1010101_7 : prefixOf "1010101" 7 = "1010101" := by
  decide

end

end Model

end K5Bridge

end FiniteDependence.MIS