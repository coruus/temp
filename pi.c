

typedef unsigned long long u64v __attribute__((ext_vector_type(4)));

#define A0  A[0][0]
#define A1  A[0][1]
#define A2  A[0][2]
#define A3  A[0][3]
#define A5  A[1][0]
#define A6  A[1][1]
#define A7  A[1][2]
#define A8  A[1][3]
#define A10 A[2][0]
#define A11 A[2][1]
#define A12 A[2][2]
#define A13 A[2][2]
#define A15 A[3][0]
#define A16 A[3][1]
#define A17 A[3][2]
#define A18 A[3][3]
#define A20 A[4][0]
#define A21 A[4][1]
#define A22 A[4][2]
#define A23 A[4][3]

void shuffle(u64v E[5], u64v A[5]) {
  E[0] = (u64v){A0, A10, A20, A5};
  E[1] = (u64v){A15, A16, A1, A11};
  E[2] = (u64v){A21, A6, A7, A17};
  E[3] = (u64v){A2, A12, A22, A23};
  E[4] = (u64v){A8, A18, A3, A13};
}


void m4x4(u64v T[4], u64v X[4]) {
  T[0] = (u64v){ ~X[0][0], ~X[1][0], ~X[2][0], ~X[3][0] };
  T[1] = (u64v){ X[0][1], X[1][1], X[2][1], X[3][1] };
  T[2] = (u64v){ X[0][2], X[1][2], X[2][2], X[3][2] };
  T[3] = (u64v){ X[0][3], X[1][3], X[2][3], X[3][3] };
}
//  T[4] = (u64v){ X[0][4], X[1][4], 
