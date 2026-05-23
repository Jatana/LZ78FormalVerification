from math import log2

def get_log(x):
    if x == 0:
        return 0
    return int(log2(x))

for n in range(1000):
    assert (get_log(n) - get_log(get_log(n)) * (n + 1 - 2 ^ (get_log(n) - get_log(get_log(n)))) >= n * (get_log(n) - 10 * get_log (get_log(n)) - 10))

