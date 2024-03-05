option solver ipopt;
option display_width 100;

param deg = 4;
param x = 8;

var Psi {0..x, 0..x} >= 0, <= 2;
var alpha >= 1.5;

minimize obj: alpha;

s.t.

P1 {c in 1..x}:
    (deg != 6) or Psi[x,c] <= 1;

P2 {c in 0..x}:
	Psi[0,c] = 0;

P3 {m in 1..x-1, c in 1..m, c1 in 1..m+1}:
	Psi[m+1,c1] >= Psi[m,c];

P4 {m in deg..x, c in 1..m, c1 in (if m == deg then {0} else 1..m-deg)}:
	(deg == 6) or Psi[m,c]-Psi[m-deg,c1] <= 1;

init {m in 1..x}:
	Psi[m,0] = 0;

init2 {m in 1..x, c in m+1..x}:
	Psi[m,c] = 0;

end_condition {c in 1..x}:
	Psi[x,c] = Psi[x,1];

# B1

B1 {m in 4..x, c in (if m == 4 then {1} else 2..m-3)}:
    2*alpha^-(2-(Psi[m,c]-Psi[m-4,c-1])) <= 1;

# B2

B2_1 {m in 2..x, c in (if m <= 2 then {1} else 2..m-1), c1 in 1..m-1}:
	alpha^-(1-(Psi[m,c]-Psi[m-1,c1])) + alpha^-(2-(Psi[m,c]-Psi[m-2,c-1])) <= 1;

B2_2 {m in 2..x, c in 1..m,
		c1 in (if m <= 5 then {0} else 1..m-5),
		c2 in (if m <= 4 then {0} else 1..m-4) }:
	alpha^-(2-(Psi[m,c]-Psi[max(0,m-5),c1])) + alpha^-(2-(Psi[m,c]-Psi[max(0,m-4),c2])) <= 1;

# We don't need to handle the vector (1-Delta(m,-1,m,c'),1) since its branching number is <= 2

B2_4 {m in 1..x, c1 in (if m <= 3 then {0} else 1..m-3), c2 in 1..m}:
	alpha^-(2-(Psi[m,m]-Psi[max(0,m-3),c1])) + alpha^-(1-(Psi[m,m]-Psi[m,c2])) <= 1;

# B3

B3_1 {m in 1..x, c1 in 1..min(x,m+1)}:
	alpha^-(1-(Psi[m,m]-Psi[m-1,m-1])) + alpha^-(1-(Psi[m,m]-Psi[min(x,m+1),c1])) <= 1;

B3_2 {m in 2..x, c in 1..m-1,
		c1 in (if m <= 2 then {0} else 1..m-2),
		c2 in (if m <= 3 then {1} else 1..m-3) : m != 4}:
	alpha^-(1-(Psi[m,c]-Psi[m-2,c1])) + alpha^-(2-(Psi[m,c]-Psi[max(0,m-4)+1,c2])) <= 1;

B3_2_4 {c in 1..3, c1 in 1..2, c2 in 1..2}:
	alpha^-(1-(Psi[4,c]-Psi[2,c1])) + alpha^-(2-(Psi[4,c]-Psi[2,c2])) <= 1;

B3_3 {d in 3..deg, m in d..x, c in 1..m-(d-1),
		c1 in (if m <= d then {0} else 1..m-d),
		c2 in (if m <= d^2 then {0} else 1..m-d^2) }:
	alpha^-(1-(Psi[m,c]-Psi[m-d,c1])) + alpha^-(d-(Psi[m,c]-Psi[max(0,m-d^2),c2])) <= 1;

B4:
	(deg != 4) or 2*alpha^-(1+Psi[1,1]) + alpha^-(3) <= 1;

# B5
# The vectors of this rule are dominated by (1,2,2) so the branching number is <= 2

#B6

B6_I0_1 {c1 in 1..5}:
	(deg not in 3..4) or alpha^-(1+Psi[5,c1]) + alpha^-(Psi[2,2]) <= 1;

B6_I0_2 {c1 in 1..4, c2 in 1..3}:
	(deg not in 3..4) or alpha^-(1+Psi[4,c1]) + alpha^-(min(1,Psi[4,2])) <= 1;

B6_I0_3 {c1 in 1..4, c2 in 1..3}:
	(deg not in 3..4) or alpha^-(1+Psi[4,c1]) + alpha^-(1+Psi[3,c2]) + alpha^-(1+Psi[2,2]) <= 1;

B6_I0_4 {c1 in 1..4, c2 in 1..2}:
	(deg not in 3..4) or alpha^-(1+Psi[4,c1]) + alpha^-(2) + alpha^-(1+Psi[2,c2]) <= 1;

B6_I1:
	(deg not in 3..4) or alpha^-(min(3,2+Psi[1,1])) + alpha^-(Psi[2,2]) <= 1;

# B8

B8 {c1 in 1..6}:
	(deg != 6) or alpha^-(1) + alpha^-(Psi[6,c1]) <= 1;

B8_R {c1 in 1..deg+1}:
	(deg not in 4..5) or alpha^-(1) + alpha^-(1+Psi[deg+1,c1]) <= 1;

B8_B2_1 {c1 in 1..deg-1, c2 in 1..deg-2}:
	(deg not in 4..5) or alpha^-(1) + alpha^-(1+Psi[deg-1,c1]) + alpha^-(2+Psi[deg-2,c2]) <= 1;

B8_B2_3 {c1 in 1..deg+1}:
	(deg not in 4..5) or alpha^-(1) + alpha^-(1+Psi[deg+1,c1]) + alpha^-(1+Psi[deg,deg]) <= 1;

#  We don't need to handle the vector (1,2,2+Psi()) since its branching number is at most 2

B8_B2_4 {c1 in 1..deg-3, c2 in 1..deg}:
	(deg not in 4..5) or alpha^-(1) + alpha^-(2+Psi[deg-3,c1]) + alpha^-(1+Psi[deg,c2]) <= 1;

B7_B3_1 {c1 in 1..deg+1}:
	(deg != 5) or alpha^-(1) + alpha^-(1+Psi[deg-1,deg-1]) + alpha^-(1+Psi[deg+1,c1]) <= 1;

B7_B3_2 {c1 in 1..3, c2 in 1..2}:
	(deg != 5) or alpha^-(1) + alpha^-(1+Psi[3,c1]) + alpha^-(2+Psi[2,c2]) <= 1;
        
B7_B3_3 {d1 in 3..deg-1, c1 in 1..deg-d1}:
	(deg != 5) or alpha^-(1) + alpha^-(1+Psi[deg-d1,c1]) + alpha^-(d1) <= 1;

B8_B3_1_d3 {c1 in 1..6}:
	(deg != 4) or alpha^-(1) + alpha^-(1+Psi[3,3]) + alpha^-(1+Psi[6,c1]) <= 1;

B8_B3_1_Ra {c1 in 1..5}:
	(deg != 4) or alpha^-(2) + alpha^-(1+Psi[3,3]) + alpha^-(1+Psi[5,c1]) <= 1;

B8_B3_1_Rb {c1 in 1..2, c2 in 1..5}:
	(deg != 4) or alpha^-(1+Psi[1,1]) + alpha^-(1+Psi[3,3]) + alpha^-(1+Psi[5,c2]) <= 1;

B8_B3_1_B4 {c1 in 1..5}:
	(deg != 4) or 2*alpha^-(2+Psi[1,1]) + alpha^-(4) + alpha^-(1+Psi[3,3]) + alpha^-(1+Psi[5,c1]) <= 1;

B8_B3_1_B5 {c1 in 1..4, c2 in 1..5}:
	(deg != 4) or alpha^-(2+Psi[4,c1]) + 2*alpha^-(3) + alpha^-(1+Psi[3,3]) + alpha^-(1+Psi[5,c2]) <= 1;

B8_B3_1_B6_I0_1 {c1 in 1..5}:
	(deg != 4) or alpha^-(2+Psi[5,c1]) + alpha^-(1+Psi[2,2]) + alpha^-(1+Psi[3,3]) + alpha^-(1+Psi[5,c1]) <= 1;

B8_B3_1_B6_I0_2 {c1 in 1..4, c2 in 1..5}:
	(deg != 4) or alpha^-(2+Psi[4,c1]) + alpha^-(min(2,1+Psi[4,2])) + alpha^-(1+Psi[3,3]) + alpha^-(1+Psi[5,c2]) <= 1;

B8_B3_1_B6_I0_3 {c1 in 1..4, c2 in 1..3, c3 in 1..5}:
	(deg != 4) or alpha^-(2+Psi[4,c1]) + alpha^-(2+Psi[3,c2]) + alpha^-(2+Psi[2,2]) + alpha^-(1+Psi[3,3]) + alpha^-(1+Psi[5,c3]) <= 1;

B8_B3_1_B6_I0_4 {c1 in 1..4, c2 in 1..2, c3 in 1..5}:
	(deg != 4) or alpha^-(2+Psi[4,c1]) + alpha^-(3) + alpha^-(2+Psi[2,c2]) + alpha^-(1+Psi[3,3]) + alpha^-(1+Psi[5,c3]) <= 1;

B8_B3_1_B6_I1 {c1 in 1..5}:
	(deg != 4) or alpha^-(min(4,3+Psi[1,1])) + alpha^-(1+Psi[2,2]) + alpha^-(1+Psi[3,3]) + alpha^-(1+Psi[5,c1]) <= 1;

B8_B3_2_R {c1 in 1..2, c2 in 1..2}:
	(deg != 4) or alpha^-(min(2,1+Psi[1,1])) + alpha^-(1+Psi[2,c1]) + alpha^-(2+Psi[2,c2]) <= 1;

B8_B3_2_B4 {c1 in 1..2}:
	(deg != 4) or 2*alpha^-(2+Psi[1,1]) + alpha^-(4) + alpha^-(1+Psi[2,c1]) + alpha^-(2+Psi[2,c1]) <= 1;

B8_B3_2_B5 {c1 in 1..4, c2 in 1..2}:
	(deg != 4) or alpha^-(2+Psi[4,c1]) + 2*alpha^-(3) + alpha^-(1+Psi[2,c2]) + alpha^-(2+Psi[2,c2]) <= 1;

B8_B3_2_B6_I0_1 {c1 in 1..5, c2 in 1..2}:
	(deg != 4) or alpha^-(2+Psi[5,c1]) + alpha^-(1+Psi[2,2]) + alpha^-(1+Psi[2,c2]) + alpha^-(2+Psi[2,c2]) <= 1;

B8_B3_2_B6_I0_2 {c1 in 1..4, c2 in 1..2}:
	(deg != 4) or alpha^-(2+Psi[4,c1]) + alpha^-(min(2,1+Psi[4,2])) + alpha^-(1+Psi[2,c2]) + alpha^-(2+Psi[2,c2]) <= 1;

B8_B3_2_B6_I0_3 {c1 in 1..4, c2 in 1..3, c3 in 1..2}:
	(deg != 4) or alpha^-(2+Psi[4,c1]) + alpha^-(2+Psi[3,c2]) + alpha^-(2+Psi[2,2]) + alpha^-(1+Psi[2,c3]) + alpha^-(2+Psi[2,c3]) <= 1;

B8_B3_2_B6_I0_4 {c1 in 1..4, c2 in 1..2, c3 in 1..2}:
	(deg != 4) or alpha^-(2+Psi[4,c1]) + alpha^-(3) + alpha^-(2+Psi[2,c2]) + alpha^-(1+Psi[2,c3]) + alpha^-(2+Psi[2,c3]) <= 1;

B8_B3_2_B6_I1 {c1 in 1..2}:
	(deg != 4) or alpha^-(min(4,3+Psi[1,1])) + alpha^-(1+Psi[2,2]) + alpha^-(1+Psi[2,c1]) + alpha^-(2+Psi[2,c1]) <= 1;

solve;
display Psi;
display alpha;
