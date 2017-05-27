#!/usr/bin/env python

import sys, os, re, argparse, random, signal, multiprocessing, Queue, threading
import numpy as np
import matplotlib.pyplot as plt

from reporting import log, log_progress, cyan, red, green, yellow
from command import Command

testcase_result = {}
profiling_db = dict()
testcases = []
benchmark_results = {} # testcase => [(seconds, memory)]
failed = False
interrupted = False

ARGS = None

BASE_PATH = os.getcwd() # os.path.dirname(os.path.realpath(__file__))

TEST_SUCCESS = 0
TEST_FAILED = 1
TEST_TIMEOUT = 2
TEST_UNKNOWN = 3

# Statistics
SUCCESSES = 0
FAILEDS = 0
TIMEOUTS = 0
UNKNOWNS = 0

SATISFIABLE = 10
UNSATISFIABLE = 20
UNKNOWN = 30
TIMEOUT = -15

categories = []
HANDMADE_INSTANCES = ['handmade']
QBFLIB2010_INSTANCES = ['qbflib2010-2QBF']
QBFEVAL2016_2QBF_INSTANCES = ['qbfeval2016-2QBF']
QBFEVAL2016_INSTANCES = ['qbfeval2016']
EVAL2012r2 = ['eval2012r2']
HARDWAREFIXPOINT = ['hardwarefixpoint']
PEC_2QBF = ['pec-2qbf']
COMPLEXITY = ['complexity']
SYNTHESIS = ['synthesis']
EASY_INSTANCES = ['easy']
RANKING = ['rankingfunctions']
RANDOM2QBF =['random2QBF']
TERMINATOR =['terminator']
HORN = ['horn']
RENHORN = ['renHorn']
RF_1133qd = ['reduction-finding-1133qd']
IRQ = ['irq']
WMI = ['wmi']
SORTING = ['sorting']
CIRCUIT_UNDERSTANDING_3QBF = ['circuit-understanding-3qbf']
HOLCOMB = ['holcomb']
SYGUS_MINITEST = ['sygus-minitest']
SYGUS_PERFORMANCE = ['sygus-performance']
SYGUS_GALLERY = ['sygus-gallery']
SYGUS_MINITEST3QBF = ['sygus-minitest3QBF']
SYGUS_PERFORMANCE3QBF = ['sygus-performance3QBF']
SYGUS_GALLERY3QBF = ['sygus-gallery3QBF']
TICTACTOE3x3 = ['gttt3x3']
TICTACTOE4x4 = ['gttt4x4']
TICTACTOE5x5 = ['gttt5x5']
TICTACTOE6x6 = ['gttt6x6']
RIENER = ['riener']
BMC2006 = ['bmc2006']
STRATEGIC_COMPANIES = ['strategiccompanies']
QREVENGE_ADDER_SELF = ['qrevenge-adder-self-2QBF']
FUNCTION_SYNTHESIS = ['function-synthesis']
ALL_INSTANCES = HANDMADE_INSTANCES + EASY_INSTANCES + QBFLIB2010_INSTANCES + QBFEVAL2016_2QBF_INSTANCES + QBFEVAL2016_INSTANCES + CIRCUIT_UNDERSTANDING_3QBF + HARDWAREFIXPOINT + PEC_2QBF + COMPLEXITY + SYNTHESIS + RANKING + RANDOM2QBF + TERMINATOR + HORN + RENHORN + RF_1133qd + IRQ + WMI + SORTING + HOLCOMB + SYGUS_MINITEST + SYGUS_PERFORMANCE + SYGUS_GALLERY + SYGUS_MINITEST3QBF + SYGUS_PERFORMANCE3QBF + SYGUS_GALLERY3QBF + TICTACTOE3x3 + TICTACTOE4x4 + TICTACTOE5x5 + TICTACTOE6x6 + EVAL2012r2 + RIENER + BMC2006 + STRATEGIC_COMPANIES + QREVENGE_ADDER_SELF + FUNCTION_SYNTHESIS
CUSTOM_INSTANCES = ['custom']
custom_instances = []

TIME_UTIL = '/usr/bin/time -v '
if sys.platform == 'darwin':
    # must be the GNU version of time (brew install gnu-time)
    TIME_UTIL = 'gtime -v '
TIME_UTIL = 'exec ' + TIME_UTIL

def log_fail(name, log):
    for line in log.split('\n'):
        if line:
            print ('> ' + line)
    print ('')

def log_return_value(name, return_value):
    if return_value == SATISFIABLE:
        result = "SAT"
    elif return_value == UNSATISFIABLE:
        result = "UNSAT"
    elif return_value == UNKNOWN:
        result = "UNKNOWN"
    else:
        result = str(return_value)
    log_progress(result)

def compute_average(results):
    seconds = 0
    memory = 0
    for s, m in results:
        seconds += s
        memory += m
    seconds /= len(results)
    memory /= len(results)
    return seconds, memory

def print_result(name,result,return_value,seconds,memory):
    if return_value == SATISFIABLE:
        return_value = "SAT"
    elif return_value == UNSATISFIABLE:
        return_value = "UNSAT"
    else:
        return_value = str(return_value)
        
    if result == TEST_FAILED:
        failed = True
        log_progress(red('FAILED:  ') + name)
    elif result == TEST_TIMEOUT:
        log_progress(yellow('TIMEOUT: ') + name)
    else:
        if result == TEST_UNKNOWN:
            log_progress(cyan('UNKNOWN: ') + name)
        else:
            log_progress(green('SUCCESS: ') + name)
    
    if seconds != None and memory != None:
        log_progress(' [{:.2f}s, {:.1f}MB]'.format(seconds, memory))
        
    log_progress('\n')
            
def print_stats():
    global failed
    print ('\nStatistics:')
    i = 0
    for name in testcases:
        if name not in testcase_result:
            continue
        i += 1
        result, return_value = testcase_result[name]
        seconds=None
        memory=None
        if name in benchmark_results:
            seconds, memory = compute_average(benchmark_results[name])
        print_result(name,result,return_value,seconds,memory)
    print ('Printed {} results in total'.format(i))
    
    log_progress(green( 'SUCCESS: ') + "{}\n".format(SUCCESSES))
    log_progress(red(   'FAILED:  ') + "{}\n".format(FAILEDS))
    log_progress(yellow('TIMEOUT: ') + "{}\n".format(TIMEOUTS))
    log_progress(cyan(  'UNKNOWN: ') + "{}\n".format(UNKNOWNS))

def write_csv(file_handle, benchmark):
    header = ['"Name"','"Result"','"time [s]"','"memory [MB]"']
    if benchmark and benchmark > 1:
        for i in xrange(benchmark):
            header.extend(['"run {} [s]"'.format(i+1), '"run {} [KB]"'.format(i+1)])
    file_handle.write('{}\n'.format(';'.join(header)))
    for name in testcases:
        if name not in testcase_result:
            continue
        result = testcase_result[name]
        row = ['"{}"'.format(name), '{}'.format(result)]
        
        if name in benchmark_results:
            seconds, memory = compute_average(benchmark_results[name])
            row.extend(['{}'.format(seconds), '{}'.format(memory)])
            if benchmark and benchmark > 1:
                for i in xrange(benchmark):
                    if i < len(benchmark_results[name]):
                        seconds, memory = benchmark_results[name][i]
                        row.extend(['{}'.format(seconds), '{}'.format(memory)])
                else:
                    row.extend(['', ''])
        else:
            row.extend(['', ''])
            if benchmark and benchmark > 1:
                for i in xrange(benchmark):
                    row.extend(['', ''])
        
        file_handle.write('{}\n'.format(';'.join(row)))

# Calls a program and returns (exit_code, output, error)
def call(cmd, timeout=None):
    cmd = Command(cmd)
    return cmd.run(ARGS.timeout, shell=True, preexec_fn=os.setsid) # http://stackoverflow.com/questions/4789837/how-to-terminate-a-python-subprocess-launched-with-shell-true


def worker_loop(job_queue, result_queue, process_id):
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    while True:
        # print 'new_iteration of thread {}'.format(process_id)
        try:
            job = job_queue.get(block=True,timeout=1) # This is hacky times out after 1 second if no element is in the queue. This terminates the tread!
            result_queue.put(run_testcase(job),block=True)
            
        except Queue.Empty:
            # print 'thread {} has an exception'.format(process_id)
            break
        # print 'thread {} finished iteration'.format(thread_id)
        # except KeyboardInterrupt:
            # print 'Worker process {} got interrupted'.format(process_id)
    # print 'thread {} ended'.format(thread_id)
    
def run_testcases(threads, runs=1):
    global interrupted, testcases
    all_testcases = getTestCases()
    
    to_run = []
    
    # Test instances
    for category in categories:
        if category in all_testcases:
            for testcase in all_testcases[category]:
                to_run.append(testcase)
    
    testcases = [name for name,_ in to_run]
    
    to_run = to_run * runs
    
    job_queue = multiprocessing.Queue()
    result_queue = multiprocessing.Queue()

    for test in to_run:
        job_queue.put(test)

    workers = []
    for i in range(threads):
        tmp = multiprocessing.Process(target=worker_loop, args=(job_queue, result_queue, i))
        tmp.start()
        workers.append(tmp)
    
    for i in range(len(to_run)):
        try:
            testcase, code, seconds, memory, return_value = result_queue.get(block=True)
            if testcase not in testcase_result:
                testcase_result[testcase] = (code, return_value)
            if seconds is not None:
                if not testcase in benchmark_results:
                    benchmark_results[testcase] = []
                benchmark_results[testcase].append((seconds, memory))
            if code == TEST_FAILED:
                global FAILEDS
                FAILEDS += 1
            elif code == TEST_SUCCESS:
                global SUCCESSES
                SUCCESSES += 1
            elif code == TEST_TIMEOUT:
                global TIMEOUTS
                TIMEOUTS += 1
            elif code == TEST_UNKNOWN:
                global UNKNOWNS
                UNKNOWNS += 1
            else:
                print ('Unexpected return code. Statistics might be affected.')
        except KeyboardInterrupt:
            interrupted = True
            for worker in workers:
                worker.terminate()
                worker.join()
            return
    
    for worker in workers:
        worker.terminate()
        worker.join()

def profile_entry(testcase,output,seconds,memory,return_value):
    
    quantifiers = None
    existential_variables = None
    universal_variables = None
    initial_clauses = None
    decisions = None
    conflicts = None
    global_conflict_checks = None
    local_determinicity_checks = None
    propagations = None
    pure_variables = None
    propagations_of_constants = None
    restarts = None
    
    parse_num = re.compile(r"[^\d]*(\d+)")
    
    for line in output.split('\n'):
        if 'Scopes:' in line:
            quantifiers = int(parse_num.match(line).groups(1)[0])
        elif 'Existential variables:' in line:
            existental_variables = int(parse_num.match(line).groups(1)[0])
        elif 'Universal variables:' in line:
            universal_variables = int(parse_num.match(line).groups(1)[0])
        elif 'Clauses:' in line:
            initial_clauses = int(parse_num.match(line).groups(1)[0])
        elif 'Conflicts:' in line:
            conflicts = int(parse_num.match(line).groups(1)[0])
        elif 'Decisions:' in line:
            decisions = int(parse_num.match(line).groups(1)[0])
        elif 'Global conflict checks:' in line:
            global_conflict_checks = int(parse_num.match(line).groups(1)[0])
        elif 'Local conflict checks:' in line:
            local_conflict_checks = int(parse_num.match(line).groups(1)[0])
        elif 'Propagations:' in line:
            propagations = int(parse_num.match(line).groups(1)[0])
        elif 'Pure variables:' in line:
            pure_variables = int(parse_num.match(line).groups(1)[0])
        elif 'Propagations of constants:' in line:
             propagations_of_constants = int(parse_num.match(line).groups(1)[0])
        elif 'Restarts:' in line:
            restarts = int(parse_num.match(line).groups(1)[0])
    
    # Composite values
    # successful_local_determinicity_checks = propagations - pure_variables - propagations_of_constants
    # variables = existential_variables + universal_variables
    # learnt_clauses_timings =
    # average_learnt_clause_size =
    # initial_average_clause_size =
    
    p = {'name':testcase,
        'seconds':seconds,
        'memory':memory,
        'return_value':return_value,
        'quantifiers':quantifiers,
        'existential_variables':existential_variables,
        'universal_variables':universal_variables,
        'initial_clauses':initial_clauses,
        'decisions':decisions,
        'conflicts':conflicts,
        'global_conflict_checks':global_conflict_checks,
        'local_determinicity_checks':local_determinicity_checks,
        'propagations':propagations,
        'pure_variables':pure_variables,
        'propagations_of_constants':propagations_of_constants,
        'restarts':restarts
        }
    
    # p.successful_local_determinicity_checks = successful_local_determinicity_checks
    # p.variables = variables
    
    profiling_db.update({testcase:p})

    for attribute, value in p.items():
        print('  {} : {}'.format(attribute, value))

def run_testcase(testcase):
    testcase, expected = testcase
    parameters = []
    if ARGS.certify:
        # random_string = ''.join(random.choice(string.ascii_uppercase + string.digits) for _ in range(N))
        cert_file = testcase+'.cert1.aig';
        parameters += ['-c', cert_file]
    
    file_path = os.path.join(BASE_PATH, testcase)
    
    if ARGS.preprocessor: 
        preprocessing_string = '{} |'.format(ARGS.preprocessor)
    else:
        preprocessing_string = ''
    
    # BLOQQER += ' --bce=1 --ble=0 --eq=0 --ve=0 --exp=1 --cce=0 --hbce=0 --hble=0'
    
    if testcase.endswith('gz'):
        if sys.platform == "linux" or sys.platform == "linux2":
            # linux
            file_reader = 'zcat'
        elif sys.platform == "darwin":
            # OS X
            file_reader = 'gzcat'
        elif sys.platform == "win32":
            # Windows...
            file_reader = 'zcat' # will not work
    else: 
        file_reader = 'cat'
    
    command_string = 'bash -c "{} {} | {} {} {} {}"'.format(   # using bash -c here because otherwise the command is executed in sh which may cause strange behavior
                        file_reader, 
                        file_path, 
                        preprocessing_string, 
                        TIME_UTIL, 
                        ARGS.tool, 
                        ' '.join(parameters))
    
    return_value, output, error = call(command_string, ARGS.timeout)
    
    if ARGS.verbose:
        print('COMMAND: ' + command_string)
        print('OUTPUT: ' + output)
        sys.stdout.flush()
    
    code = None
    seconds = None
    memory = None
    
    if return_value in [UNKNOWN,SATISFIABLE,UNSATISFIABLE]:
        seconds, memory = get_benchmark_result(testcase, error)
        
    if return_value == TIMEOUT:
        code = TEST_TIMEOUT
    elif return_value == UNKNOWN:
        code = TEST_UNKNOWN
    elif return_value in [SATISFIABLE,UNSATISFIABLE] and (return_value == expected or expected == UNKNOWN):
        code = TEST_SUCCESS
    else:
        code = TEST_FAILED
            
    print_result(testcase,code,return_value,seconds,memory)
    
    if code == TEST_FAILED:
        log_fail(testcase, output + error)
    elif ARGS.statistics:
        print('\nOutput for command ' + command_string + '\n' + output)
        sys.stdout.flush()
    
    if ARGS.profile:
        profile_entry(testcase,output,seconds,memory,return_value)
    
    if ARGS.certify and return_value == SATISFIABLE:
        print("CERTIFYING NOW")
        cert_return_value, cert_output, cert_error = call('abc -c "read ' + cert_file + 'tmp.aig; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2;  print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; print_stats; dc2; write ' + cert_file + ';"',ARGS.timeout);

        cert_file2 = testcase+'.cert2.aig';

        cert_cmd = './../tools/caqe/certcheck ' + testcase + ' ' + cert_file + ' | aigtoaig - ' + cert_file2
        cert_return_value, cert_output, cert_error = call(cert_cmd, ARGS.timeout)
        
        # print(cert_cmd)
        # print(cert_output)
        # print(cert_error)
        
        cert_return_value, cert_output, cert_error = call('abc -c "&r ' + cert_file2 + '; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &put; write ' + cert_file2 + '"', ARGS.timeout);
        
        cert_return_value, cert_output, cert_error = call('cat '+cert_file2+' | aigtocnf | lingeling', 5 *  ARGS.timeout)
        
        if 's UNSATISFIABLE' not in cert_output:
            print('CERTIFICATE FAILED!')
            code = TEST_FAILED
            if ARGS.verbose:
                print('Cert Output:\n' + cert_output)
                print('Cert Error:\n' + cert_error)
        else:
            # if ARGS.verbose:
            print('Certified!')
            
        call('rm ' + cert_file + ' ' + cert_file2, ARGS.timeout)
        
    return testcase, code, seconds, memory, return_value

def getTestCases():
    
    test_cases = {}
    
    if ARGS.directory:
        test_cases['directory'] = []
        for (dirpath, dirnames, filenames) in os.walk(ARGS.directory):
            # print ('dirpath' + dirpath + '\n')
            # for dn in dirnames:
                # print ('  dn: ' + dn + '\n')
            # file_count = 0
#             for fn in filenames:
#                 file_count += 1
#             print("Detected {} files".format(file_count))
#             exit(1)
            omitted_files = 0
            detected_files = 0
            for filename in filenames:
                if filename.endswith('qdimacs.gz') or filename.endswith('aag') or filename.endswith('aig') or filename.endswith('qdimacs'):
                    value = (os.path.join(ARGS.directory,filename),30)
                    test_cases['directory'].append(value)
                    detected_files += 1
                else:
                    omitted_files += 1
            print("Detected {} files in directory {}".format(detected_files,ARGS.directory))
            if omitted_files > 0:
                print("Omitted {} files".format(omitted_files))
        return test_cases
    else:
        file_handle = open(os.path.join(BASE_PATH, 'integration-tests', 'instances.txt'))
        category_re = re.compile(r"\[(.*?)\]")
    
        test_cases['custom'] = []
    
        last_category = []
        for line in file_handle:
            line = line.strip()
            if not line: # ignore empty lines
                continue
        
            match = category_re.match(line)
            if match:
                if last_category:
                    assert category
                    test_cases[category] = last_category
                last_category = []
                category = match.group(1)
            else:
                test_case, return_value = [v.strip() for v in line.split('|')]
                values = (test_case, int(return_value))
                last_category.append(values)
            
                # get correct result for custom selection
                if test_case in custom_instances and values not in test_cases['custom']:
                    test_cases['custom'].append(values)
    
        test_cases[category] = last_category
        return test_cases

def get_benchmark_result(testcase, time_output):
    wall_clock_re = re.compile(r"[^\d]*(\d+):(\d+\.\d+)")
    wall_clock_long_re = re.compile(r"[^\d]*(\d+):(\d+):(\d+)")
    memory_re = re.compile(r"[^\d]*(\d+)")
    
    
    for line in time_output.split('\n'):
        if 'Elapsed (wall clock) time' in line:
            match = wall_clock_re.match(line)
            hours = "0"
            if match:
                minutes, seconds = match.groups()
            else:
                hours, minutes, seconds = wall_clock_long_re.match(line).groups()
            seconds = int(hours)*3600 + int(minutes)*60 + float(seconds)
        elif 'Maximum resident set size' in line:
            memory = int(memory_re.match(line).group(1))
        elif 'Minor (reclaiming a frame) page faults' in line:
            page_faults = int(memory_re.match(line).group(1))
        elif 'Page size (bytes)' in line:
            page_size = int(memory_re.match(line).group(1))/1024
    
    if sys.platform == 'darwin':
        # estimate memory consumption by page faults:
        memory = page_faults*page_size
        
    return float(seconds), float(memory) / 1024.0

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('-v', '--verbose', dest='verbose', action='store_true',
                        help='Additional debug output for the tester tool')
    parser.add_argument('-s', '--statistics', dest='statistics', action='store_true',
                        help='Show additional runtime information (tool output)')
    parser.add_argument('-t', '--test', dest='test', action='store_true',
                        help='Run on a subset of test benchmarks')
    parser.add_argument('--benchmark', action='store', nargs='?', const=5, type=int, metavar='rounds',
                        help='Run the tests multiple times and take the average')
    parser.add_argument('--timeout', dest='timeout', action='store', type=int, default=10,
                        help='Timeout in seconds (default: 10)')
    parser.add_argument('--csv', dest='csv', action='store', nargs='?', const='tester.csv', metavar='file_name', type=argparse.FileType('w'),
                        help='Write CSV to file (default: tester.csv)')
    parser.add_argument('--threads', dest='threads', action='store', nargs='?', type=int, metavar='num', default=1,
                        help='Number of threads to use (default: {})'.format(multiprocessing.cpu_count()))
    parser.add_argument('instances', nargs='*',
                        help='Instances to run the tester on')
    parser.add_argument('--tool', dest='tool', action='store', default=os.path.join(BASE_PATH, './cadet -v 1'), help='provide an alternative tool name, E.g. depqbf depqbf5.0 rareqs caqe qesto quantor ...')
    parser.add_argument('--bloqqer', dest='use_bloqqer', action='store_true', 
                        help='Use bloqqer to preprocess the formulas.')
    parser.add_argument('--preprocessor', dest='preprocessor', action='store', default=None, help='Use this command to set a preprocessor command.')
    parser.add_argument('--optimize_params_bloqqer', dest='bloqqer_params', action='store_true',
                        help='Find to find optimal parameters of bloqqer.')
    parser.add_argument('--certify', dest='certify', action='store_true',
                        help='Also test certificates. CADET only.')
    parser.add_argument('-d', '--directory', dest='directory', action='store', default=None,
                        help='Specify folder of instances to execute.')
    parser.add_argument('-p', '--profile', dest='profile', action='store_true', default=None,
                        help='Run in profiling mode. Evaluate statistics.')
                        
    for instance in ALL_INSTANCES:
        parser.add_argument('--{}'.format(instance), dest=instance, action='store_true', help='Run the {} instances'.format(instance))

    ARGS = parser.parse_args()
    
    if ARGS.test:
        print('Test mode')
        ARGS.all = False
        ARGS.benchmark = False
        ARGS.timeout = 5
        ARGS.csv = False
        ARGS.threads = 1
        ARGS.instances = None
        # ARGS.certify = False
        categories = ['test']
    
    if ARGS.instances:
        categories = CUSTOM_INSTANCES
        custom_instances = ARGS.instances
    
    if ARGS.directory:
        categories = ['directory']
    
    for instance in ALL_INSTANCES:
        if getattr(ARGS, instance):
            if not instance in categories:
                categories.append(instance)
        
    if not categories:
        parser.print_help()
        exit()
    
    if ARGS.use_bloqqer:
        ARGS.preprocessor = 'bloqqer'
    
    # Run the tests
    if ARGS.benchmark:
        run_testcases(ARGS.threads, ARGS.benchmark)
    else:
        run_testcases(ARGS.threads)
    
    # if ARGS.profile:
#         for key, data in profiling_db.items():
#             print(key)
#             for attribute, value in data.items():
#                 print('{} : {}'.format(attribute, value))
    
    print_stats()
    
    if ARGS.csv:
        write_csv(args.csv, args.benchmark)

    if failed:
        sys.exit(1)
    
    if interrupted:
        print('Interrupted by user')
        sys.exit(1)
