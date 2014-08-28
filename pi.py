s = ''' 0 ->  0
 1 -> 10
 2 -> 20
 3 ->  5
 4 -> 15
 5 -> 16
 6 ->  1
 7 -> 11
 8 -> 21
 9 ->  6
10 ->  7
11 -> 17
12 ->  2
13 -> 12
14 -> 22
15 -> 23
16 ->  8
17 -> 18
18 ->  3
19 -> 13
20 -> 14
21 -> 24
22 ->  9
23 -> 19
24 ->  4'''.replace('>', '').replace(' ', '').strip()

atoe = [n.split('-') for n in s.split('\n')]
atoe = [(int(a), int(b)) for a, b in atoe]
etoa = [(b, a) for a, b in atoe]

AtoE = dict(atoe)
EtoA = dict(etoa)

E = EtoA

for i in range(0, 25, 5):
  print("y{:02}   = {{ A[{:2}], A[{:2}], A[{:2}], A[{:2}] }}"
        .format(i, i, i+1, i+2, i+3))

print

for i in range(0, 25, 5):
  print("x{}_0 = {{ A[{:2}], A[{:2}], A[{:2}], A[{:2}] }}"
        .format(i, E[i+0], E[i+1], E[i+2], E[i+3]))
  print("x{}_1 = {{ A[{:2}], A[{:2}], A[{:2}], A[{:2}] }}"
        .format(i, E[i+1], E[i+2], E[i+3], E[i+4]))
  print("x{}_2 = {{ A[{:2}], A[{:2}], A[{:2}], A[{:2}] }}"
        .format(i, E[i+2], E[i+3], E[i+4], E[i+0]))
  print



#for a, e in atoe:
#  if a < 16 and e < 16:
#    print "mov E({e}), A({a})".format(a=a, e=e)
#print
#for a, e in atoe:
#  if a >= 16 and e < 16:
#    print "mov E({e}), A({a})".format(a=a, e=e)
#print
#for a, e in atoe:
#  if a >= 16 and e >= 16:
#    print "mov E({e}), A({a})".format(a=a, e=e)
#print
#for a, e in atoe:
#  if a < 16 and e >= 16:
#    print "mov E({e}), A({a})".format(a=a, e=e)

