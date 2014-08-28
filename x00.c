typedef unsigned long long v __attribute__((ext_vector_type(4)));
void test(v* x00, v y00, v y05, v y10, v y15, unsigned long long A24)
{
x00[0]= (v){ y00[0], y05[1], y10[2], y15[3] };
x00[1]= (v){ y05[1], y10[2], y15[3], A24    };
x00[2]= (v){ y10[2], y15[3], A24,    y00[0] };
}
