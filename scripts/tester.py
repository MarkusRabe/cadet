#!/usr/bin/env python3

import sys
import os
import re
import argparse
import random
import signal
import multiprocessing
import queue
import threading
import itertools

from reporting import log, log_progress, cyan, red, green, yellow
from command import call_interruptable

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
configs = [''] # configurations to run the tool in

TIME_UTIL = '/usr/bin/time -v '
if sys.platform == 'darwin':
    # must be the GNU version of time (brew install gnu-time)
    TIME_UTIL = 'gtime -v '
TIME_UTIL = 'exec ' + TIME_UTIL


def log_fail(name, log):
    for line in log.split(b'\n'):
        line = line.decode()
        if line:
            print('> ' + line)
    print('')


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


def print_result(name, config, expected, result, return_value, seconds, memory):
    if return_value == SATISFIABLE:
        return_value = "SAT"
    elif return_value == UNSATISFIABLE:
        return_value = "UNSAT"
    else:
        return_value = str(return_value)
        
    if result == TEST_FAILED:
        failed = True
        log_progress(red('FAILED:  '))
    elif result == TEST_TIMEOUT:
        log_progress(yellow('TIMEOUT: '))
    else:
        if result == TEST_UNKNOWN:
            log_progress(cyan('UNKNOWN: '))
        else:
            log_progress(green('SUCCESS: '))
        
    if seconds != None and memory != None:
        log_progress('[{:.2f}s, {:.1f}MB] '.format(seconds, memory))
    
    log_progress(name + ' ' + config)
    log_progress('\n')


def print_stats():
    global failed
    print('\nStatistics:')
    
    for name in testcases:
        if name not in testcase_result:
            continue
    # for x, (testcase_name, config, expected, result, return_value, seconds, memory) in sorted(testcase_result.iteritems(), key=lambda (k,v): (v,k)):
        testcase_name, config, expected, result, return_value, seconds, memory = testcase_result[name]
        print_result(testcase_name,config,expected,result,return_value,seconds,memory)
    print('Printed {} results in total'.format(len(testcase_result)))
    
    log_progress(green( 'SUCCESS: ') + "{}\n".format(SUCCESSES))
    log_progress(red(   'FAILED:  ') + "{}\n".format(FAILEDS))
    log_progress(yellow('TIMEOUT: ') + "{}\n".format(TIMEOUTS))
    log_progress(cyan(  'UNKNOWN: ') + "{}\n".format(UNKNOWNS))


def write_csv(file):
    header = ['"Formula"', '"Arguments"','"Result"','"time [s]"','"memory [MB]"','"certificate size [gates]"']
    file.write(','.join(header) + '\n')

    print(testcase_result)

    for name, data in testcase_result.iteritems():
        testcase_name, config, expected, result, return_value, seconds, memory, certificate_size = data
        row = [testcase_name,
               config,
               str(return_value),
               str(seconds),
               str(memory),
               str(certificate_size)
              ]
        file.write(','.join(row) + '\n')


def worker_loop(job_queue, result_queue, process_id):
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    while True:
        # print 'new_iteration of thread {}'.format(process_id)
        try:
            job = job_queue.get(block=True,timeout=1) # This is hacky; times out after 1 second if no element is in the queue. This terminates the tread!
            result_queue.put(run_testcase(job), block=True)
            
        except queue.Empty:
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
            for (path,result) in all_testcases[category]:
                for config in configs:
                    assert(result in [10, 20, 30])
                    if config.startswith("RESULT_SAT"):
                        c = config[len("RESULT_SAT"):]
                        r = 10
                    else:
                        c = config
                        r = result
                    to_run.append((path, r, c))
    
    testcases = [name + ' ' + config for name,_,config in to_run]
    
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
            testcase, config, expected, result, return_value, seconds, memory = result_queue.get(block=True)
            if testcase + ' ' + config not in testcase_result:
                testcase_result[testcase + ' ' + config] = (testcase, config, expected, result, return_value, seconds, memory)
            if seconds is not None:
                if not testcase in benchmark_results:
                    benchmark_results[testcase] = []
                benchmark_results[testcase].append((seconds, memory))
            if result == TEST_FAILED:
                global FAILEDS
                FAILEDS += 1
            elif result == TEST_SUCCESS:
                global SUCCESSES
                SUCCESSES += 1
            elif result == TEST_TIMEOUT:
                global TIMEOUTS
                TIMEOUTS += 1
            elif result == TEST_UNKNOWN:
                global UNKNOWNS
                UNKNOWNS += 1
            else:
                print('Unexpected return code. Statistics might be affected.')
        except KeyboardInterrupt:
            interrupted = True
            for worker in workers:
                worker.terminate()
                worker.join()
            return
    
    for worker in workers:
        worker.terminate()
        worker.join()


def profile_entry(testcase, output, seconds, memory, return_value):
    
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
    
    profiling_db.update({testcase:p})
    
    for attribute, value in p.items():
        print('  {} : {}'.format(attribute, value))


def run_testcase(testcase_input):
    testcase, expected, config = testcase_input
    parameters = config.split()
    if ARGS.certify:
        # random_string = ''.join(random.choice(string.ascii_uppercase + string.digits) for _ in range(N))
        cert_file = testcase+'.cert1.aig';
        parameters += ['-c', cert_file, '--caqecert']
    
    file_path = os.path.join(BASE_PATH, testcase)
    
    if ARGS.preprocessor: 
        preprocessing_string = '{} |'.format(ARGS.preprocessor)
    else:
        preprocessing_string = ''
    
    # BLOQQER += ' --bce=1 --ble=0 --eq=0 --ve=0 --exp=1 --cce=0 --hbce=0 --hble=0'
    
    if testcase.endswith('.gz'):
        if sys.platform == "linux" or sys.platform == "linux2":
            # linux
            file_reader = 'zcat'
        elif sys.platform == "darwin":
            # OS X
            file_reader = 'gzcat'
        elif sys.platform == "win32":
            # Windows...
            file_reader = 'zcat' # will not work
        
        # using bash -c to run the command because otherwise sh may be used on some machines
        command_string = 'bash -c "{} {} | {} {} {} {}"'.format(
                            file_reader, 
                            file_path, 
                            preprocessing_string, 
                            TIME_UTIL, 
                            ARGS.tool, 
                            ' '.join(parameters))
    else: 
        # using bash -c to run the command because otherwise sh may be used on some machines
        command_string = 'bash -c "{} {} {} {} {}"'.format(
                            preprocessing_string, 
                            TIME_UTIL, 
                            ARGS.tool, 
                            ' '.join(parameters), 
                            file_path)
    
    return_value, output, error = call_interruptable(command_string, ARGS.timeout)
    
    if ARGS.verbose:
        print('COMMAND: ' + command_string)
        print('OUTPUT: ' + output)
        sys.stdout.flush()
    
    result = None
    seconds = None
    memory = None
    
    if return_value in [UNKNOWN,SATISFIABLE,UNSATISFIABLE]:
        seconds, memory = get_benchmark_result(testcase, error)
        
    if return_value == TIMEOUT:
        result = TEST_TIMEOUT
    elif return_value == UNKNOWN:
        result = TEST_UNKNOWN
    elif return_value in [SATISFIABLE,UNSATISFIABLE] and (return_value == expected or expected == UNKNOWN):
        result = TEST_SUCCESS
    else:
        result = TEST_FAILED
            
    print_result(testcase, config, expected, result, return_value, seconds, memory)
    
    if result == TEST_FAILED:
        log_fail(testcase, output + error)
    elif ARGS.statistics:
        print('\nOutput for command ' + command_string + '\n' + output)
        sys.stdout.flush()
    
    if ARGS.profile:
        profile_entry(testcase,output,seconds,memory,return_value)
    
    if ARGS.certify and return_value == SATISFIABLE:
        print("CERTIFYING NOW")
        cert_return_value, cert_output, cert_error = \
            call_interruptable('abc -c "read ' + cert_file + 
                 'tmp.aig; print_stats; dc2; print_stats; dc2; print_stats; '
                 'dc2; print_stats; dc2; print_stats; dc2;  print_stats; dc2; '
                 'print_stats; dc2; print_stats; dc2; print_stats; dc2; '
                 'print_stats; dc2; print_stats; dc2; print_stats; dc2; '
                 'print_stats; dc2; print_stats; dc2; print_stats; dc2; '
                 'print_stats; dc2; print_stats; dc2; print_stats; dc2; '
                 'print_stats; dc2; print_stats; dc2; write ' + 
                 cert_file + ';"',ARGS.timeout);

        cert_file2 = testcase+'.cert2.aig';

        cert_cmd = './../../tools/caqe/certcheck ' + testcase + ' ' + cert_file + ' | aigtoaig - ' + cert_file2
        cert_return_value, cert_output, cert_error = call_interruptable(cert_cmd, ARGS.timeout)
        
        # print(cert_cmd)
        # print(cert_output)
        # print(cert_error)
        
        cert_return_value, cert_output, cert_error = \
            call_interruptable('abc -c "&r ' + cert_file2 + 
                 '; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; '
                 '&ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; '
                 '&ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; '
                 '&ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; &ps; &dc2; '
                 '&ps; &put; write ' + 
                 cert_file2 + '"', ARGS.timeout);
        
        cert_return_value, cert_output, cert_error = call_interruptable('cat '+cert_file2+' | aigtocnf | lingeling', 5 *  ARGS.timeout)
        
        if 's UNSATISFIABLE' not in cert_output:
            print('CERTIFICATE FAILED for {}'.format(str(testcase)))
            result = TEST_FAILED
            if ARGS.verbose:
                print('Cert Output:\n' + cert_output)
                print('Cert Error:\n' + cert_error)
        else:
            # if ARGS.verbose:
            print('Certified!')
            
        call_interruptable('rm ' + cert_file + ' ' + cert_file2, ARGS.timeout)
    return testcase, config, expected, result, return_value, seconds, memory


def getTestCases():
    
    test_cases = {}
    
    if ARGS.directory:
        test_cases['directory'] = []
        for (dirpath, dirnames, filenames) in os.walk(ARGS.directory):
            omitted_files = 0
            detected_files = 0
            for filename in filenames:
                if filename.endswith('qdimacs.gz') or filename.endswith('aag') or filename.endswith('aig') or filename.endswith('qdimacs'):
                    value = (os.path.join(dirpath,filename),30)
                    test_cases['directory'].append(value)
                    detected_files += 1
                else:
                    omitted_files += 1
            print("Detected {} files in directory {}".format(detected_files,dirpath))
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
    
        test_cases[category] = last_category
        return test_cases


def get_benchmark_result(testcase, time_output):
    wall_clock_re = re.compile(r"[^\d]*(\d+):(\d+\.\d+)")
    wall_clock_long_re = re.compile(r"[^\d]*(\d+):(\d+):(\d+)")
    memory_re = re.compile(r"[^\d]*(\d+)")
    
    
    for line in time_output.split(b'\n'):
        line = line.decode()
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
    print('')
    parser = argparse.ArgumentParser()
    parser.add_argument('-v', '--verbose', dest='verbose', action='store_true',
                        help='Additional debug output for the tester tool')
    parser.add_argument('-s', '--statistics', dest='statistics', action='store_true',
                        help='Show additional runtime information (tool output)')
    parser.add_argument('-t', '--test', dest='test', action='store_true',
                        help='Run on a subset of test benchmarks')
    parser.add_argument('--average', action='store', nargs='?', const=5, type=int, 
                        metavar='rounds',
                        help='Run the tests multiple times and take the average')
    parser.add_argument('--timeout', dest='timeout', action='store', type=int, default=10,
                        help='Timeout in seconds (default: 10)')
    parser.add_argument('--csv', dest='csv', action='store', nargs='?', const='tester.csv',
                        metavar='file_name', type=argparse.FileType('w'),
                        help='Write CSV to file (default: tester.csv)')
    parser.add_argument('--threads', dest='threads', action='store', nargs='?', type=int,
                        metavar='num', default=1,
                        help='Number of threads to use (default: {})'.format(multiprocessing.cpu_count()))
    parser.add_argument('--tool', dest='tool', action='store', 
                        default=os.path.join(BASE_PATH, './cadet -v 1'), 
                        help='Define which tool is tested (default "./cadet -v 1").')
    parser.add_argument('--config', metavar='C', type=str, nargs='*', 
                        help='provide a list of command line configurations to run \
                        the tool in; to avoid interpreting them as options for this \
                        tester script, try e.g. " --cegar" instead')
    parser.add_argument('--bloqqer', dest='use_bloqqer', action='store_true', 
                        help='Use bloqqer to preprocess the formulas.')
    parser.add_argument('--preprocessor', dest='preprocessor', action='store', default=None, 
                        help='Use this command to set a preprocessor command.')
    parser.add_argument('--certify', dest='certify', action='store_true',
                        help='Also test certificates. CADET only.')
    parser.add_argument('-d', '--directory', dest='directory', action='store', default=None,
                        help='Specify folder of formulas to solve.')
    parser.add_argument('-p', '--profile', dest='profile', action='store_true', default=None,
                        help='Run in profiling mode. Evaluate statistics.')
    parser.add_argument('-f', '--force', dest='force', action='store_true', default=None,
                        help='Override CPU load check.')
                        
    instances_file = open('integration-tests/instances.txt', 'r').read()
    all_categories = re.findall(r'\[([A-Za-z0-9_-]+)\]', instances_file)
    for cat in all_categories:
        parser.add_argument('--{}'.format(cat), dest=cat, action='store_true', 
                            help='Run the {} formulas'.format(cat))
    
    ARGS = parser.parse_args()
    
    if ARGS.test:
        print('Test mode')
        ARGS.all = False
        ARGS.timeout = 5
        ARGS.csv = False
        ARGS.threads = 4
        ARGS.instances = None
        # ARGS.certify = False
        categories = ['test_files']
        configs = ['',
                   '--cegar',
                   '--case_splits',
                   '--cegar --case_splits',
                   '--debugging --sat_by_qbf -c cert.aag',
                   'RESULT_SAT --debugging --sat_by_qbf -f cert.aag',
                   'RESULT_SAT --debugging --sat_by_qbf -e cert.aag',
                   'RESULT_SAT --debugging --sat_by_qbf -e cert.aag --cegar',
                   '--debugging --sat_by_qbf --cegar -c cert.aag',
                   # '--debugging --sat_by_qbf --case_splits -c cert.aag',
                   '--debugging --sat_by_qbf --cegar',
                   '--debugging --sat_by_qbf --cegar --case_splits',
                   '--rl --rl_mock --sat_by_qbf',
                   '--rl --rl_mock --sat_by_qbf --debugging',
                   '--rl --rl_mock --sat_by_qbf --debugging --minimize --rl_vsids_rewards',
                   '--rl --rl_mock --sat_by_qbf --random_decisions --rl_vsids_rewards',
                   '--rl --rl_mock --sat_by_qbf --random_decisions --rl_advanced_rewards --rl_vsids_rewards --rl_slim_state',
                   '--debugging -l 10 --sat_by_qbf --random_decisions --fresh_seed'
                   ]
    
    if ARGS.config:
        configs = []
        for c in ARGS.config:
            configs.append(c)
    
    if ARGS.directory:
        categories = ['directory']
    
    for cat in all_categories:
        if getattr(ARGS, cat):
            if not cat in categories:
                categories.append(cat)
    if not categories:
        parser.print_help()
        exit()
    
    if ARGS.use_bloqqer:
        ARGS.preprocessor = 'bloqqer'
    
    try:
        import psutil
        cpu_load = psutil.cpu_percent(interval=1, percpu=True)
        print('CPU load: ' + str(cpu_load))
        total_cpu_load = sum(cpu_load)
        if (sum(cpu_load) > 50.0):
            if (not ARGS.force):
                print('Error: CPU load too high. Use -f to force.')
                sys.exit(1)
            else: 
                print('Warning: CPU load high and override used.')
    except ImportError:
        print('Warning: Could not check CPU load.')
        pass # module doesn't exist, deal with it.
    
    # Run the tests
    run_testcases(ARGS.threads)
    
    print_stats()
    
    if ARGS.csv:
        write_csv(ARGS.csv)

    if failed:
        sys.exit(1)
    
    if interrupted:
        print('Interrupted by user')
        sys.exit(1)
