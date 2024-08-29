import os
import sys

def find_all_between(s: str, start: str, end: str):
    res = []
    i = 0
    while i < len(s):
        j = s.find(start, i)
        if j == -1:
            break
        k = s.find(end, j)
        if k == -1:
            break
        res.append(s[j+len(start):k])
        i = k + len(end)
    return res

def count_proof_lines(filename: str):
    with open(filename, 'r') as f:
        src = f.read()
        contents = find_all_between(src, 'Proof.', 'Qed.')
        count = 0
        for s in contents:
            count += s.strip().count('\n') + 1
        return count

def pad(s: str, n):
    if len(s) < n:
        return s + ' ' * (n - len(s))
    else:
        return s

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: proofcount.py <directory> <directory> ...')
        sys.exit(1)
    dirs = []
    line_cnts = []
    path_cnts = []
    for dirpath in sys.argv[1:]:
        line_cnt = 0
        path_cnt = 0
        for f in os.listdir(dirpath):
            if f.endswith('_verif.v'):
                line_cnt += count_proof_lines(os.path.join(dirpath, f))
                path_cnt += 1
        dirs.append(dirpath)
        line_cnts.append(line_cnt)
        path_cnts.append(path_cnt)
    leftlen = max(map(len, dirs)) + 4
    for d, c1, c2 in zip(dirs, line_cnts, path_cnts):
        print(pad(pad(d, leftlen) + str(c1), leftlen + 4) + str(c2))
