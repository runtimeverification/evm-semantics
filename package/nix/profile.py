#! /usr/bin/env nix-shell
#! nix-shell -i python3 -p python3

import sys

logfile_1 = sys.argv[1]
logfile_2 = sys.argv[2]
mintime   = 2.0
minchange = 0.035
if len(sys.argv) > 4:
    mintime   = float(sys.argv[3])
    minchange = float(sys.argv[4])

def readData(file_name):
    data_lines = []
    with open(file_name, 'r') as file_data:
        for _ in range(2):
          next(file_data)
        rev = next(file_data).strip('\n').split(':')[1].strip()
        next(file_data)
        next(file_data)
        for line in file_data:
            data_line = line.strip('\n').split(' ')
            test_index = 0
            if 'prove' in data_line:
                test_index = data_line.index('prove') + 1
            elif 'interpret' in data_line:
                test_index = data_line.index('interpret') + 1
            data_lines.append(('/'.join(data_line[test_index].split('/')[-3:]), int(data_line[0]), float(data_line[1][0:-1]), int(data_line[4][0:-2])))
    return (rev,data_lines)

def getCommitLogname(file_name):
    if file_name.startswith('.build/logs'):
        [_, _, log_name] = file_name.split('/')
        return ('HEAD', log_name)
    [_, commit, _, log_name]  = file_name.split('/')
    return (commit, log_name)

data_entries = {}
(key1, data1) = readData(logfile_1)
data_entries[key1] = { test : ( rc , time , mem ) for (test, rc, time, mem) in data1 }
(key2, data2) = readData(logfile_2)
data_entries[key2] = { test : ( rc , time , mem ) for (test, rc, time, mem) in data2 }


common_passing_tests = []
for test in data_entries[key1].keys():
    if data_entries[key1][test][0] == 0 and test in data_entries[key2].keys() and data_entries[key2][test][0] == 0:
        common_passing_tests.append(test)

def filterEntries(test, t1, t2):
    return (t1 != t2)                                                   \
       and (t1 > mintime or t2 > mintime)                               \
       and ((t1 / t2) - 1.0 > minchange or (t2 / t1) - 1.0 > minchange)

# test , time1 , time2 , time1 / time2
final_table = []
for test in common_passing_tests:
    (_, time1, _) = data_entries[key1][test]
    (_, time2, _) = data_entries[key2][test]
    if filterEntries(test, time1, time2):
        final_table.append((test, time1, time2, time1 / time2))
final_table.sort(key = lambda e: e[3])
if len(final_table) == 0:
    print("Identical runs")
    sys.exit(0)
total_time_1 = sum([e[1] for e in final_table])
total_time_2 = sum([e[2] for e in final_table])
if total_time_2 > 0.0:
    final_table.append(('TOTAL', total_time_1, total_time_2, total_time_1 / total_time_2))
final_table = [ (str(e0), str(e1), str(e2), str(e3)) for (e0, e1, e2, e3) in final_table ]
final_table.insert(0, ('Test', key1 + ' time', key2 + ' time', '(' + key1 + '/' + key2 + ') time'))
final_table.insert(1, ('', '', '', ''))

column_width0 = max([len(c[0]) for c in final_table])
column_width1 = max([len(c[1]) for c in final_table])
column_width2 = max([len(c[2]) for c in final_table])
column_width3 = max([len(c[3]) for c in final_table])

def mkColumn(c, w):
    return ' ' + c.ljust(w) + ' '

columns = ['|'.join((mkColumn(c0, column_width0), mkColumn(c1, column_width1), mkColumn(c2, column_width2), mkColumn(c3, column_width3))) for (c0, c1, c2, c3) in final_table]
columns[1] = columns[1].replace(' ', '-')

print('\n'.join(columns))
