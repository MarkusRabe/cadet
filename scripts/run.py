#!/usr/bin/env python3

import sys
import os
import re
import argparse
import signal
import multiprocessing as mp
import queue
import tempfile

from reporting import log, log_progress, cyan, red, green, yellow
from command import call_interruptable
from subprocess import PIPE, call

failed = False
interrupted = False

BASE_PATH = os.getcwd() # os.path.dirname(os.path.realpath(__file__))

TIME_UTIL = '/usr/bin/time -v '
if sys.platform == 'darwin':
    # must be the GNU version of time (brew install gnu-time)
    TIME_UTIL = 'gtime -v '
TIME_UTIL = 'exec ' + TIME_UTIL


def log_fail(log):
    for line in log.split('\n'):
        if line:
            print('> ' + line)
    print('')


def print_result(name, config, expected, result, return_value, seconds, memory):
    global failed

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


def jobs_from_paths(paths, configs):
    jobs = {}
    for name, (path, expected) in paths.items():
        for config in configs:
            assert expected in [10, 20, 30]
            if 'RESULT_SAT' in config:
                config = config.replace('RESULT_SAT','')
                expected = 10
            jobs[f'{config} {name}'] = (f'{config} {path}', expected)
    return jobs


def get_paths_from_categories(categories, directory):
    paths = {}

    if directory:
        for (dirpath, dirnames, filenames) in os.walk(directory):
            omitted_files = 0
            detected_files = 0
            for filename in filenames:
                if filename.endswith('.qdimacs.gz') or \
                   filename.endswith('.aag') or \
                   filename.endswith('.aig') or \
                   filename.endswith('.qdimacs'):

                    paths[os.path.join(dirpath,filename)] = (os.path.join(dirpath,filename), 30)
                    detected_files += 1
                else:
                    omitted_files += 1
            print(f'Detected {detected_files} files in directory {dirpath}')
            if omitted_files > 0:
                print(f'Omitted {omitted_files} files')

    categories_file = os.path.join(BASE_PATH, 'integration-tests', 'instances.txt')
    with open(categories_file) as file_handle:
        category_re = re.compile(r"\[(.*?)\]")
        active_category = False
        for line in file_handle:
            line = line.strip()
            if not line: # ignore empty lines
                continue
        
            match = category_re.match(line)
            if match:
                if match.group(1) in categories:
                    print(f'Detected category {match.group(1)}')
                    active_category = True
                else:
                    active_category = False
            else:
                if active_category:
                    path, expected_result = [v.strip() for v in line.split('|')]
                    expected_result = int(expected_result)
                    directory, file_name = os.path.split(path)
                    if file_name in paths:
                        paths[path] = (f'{path}', expected_result)
                    else:
                        paths[file_name] = (f'{path}', expected_result)
    return paths


def halt_if_busy(ARGS):
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


def get_benchmark_result(time_output):
    wall_clock_re = re.compile(r"[^\d]*(\d+):(\d+\.\d+)")
    wall_clock_long_re = re.compile(r"[^\d]*(\d+):(\d+):(\d+)")
    memory_re = re.compile(r"[^\d]*(\d+)")
    seconds = None
    memory = None
    page_faults = None
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
            memory = float(memory_re.match(line).group(1)) / 1024.0
        elif 'Minor (reclaiming a frame) page faults' in line:
            page_faults = int(memory_re.match(line).group(1))
        elif 'Page size (bytes)' in line:
            page_size = int(memory_re.match(line).group(1))/1024
    if sys.platform == 'darwin':
        # estimate memory consumption by page faults:
        if page_faults:  # could be None in case of timeout
            memory = float(page_faults*page_size) / 1024.0
    return seconds, memory


def minimize_certificate(f):
    call(
        [
         "abc", "-c",
         f"read {f.name}; print_stats;dc2;dc2;dc2;print_stats; write {f.name}"
        ],
        stdout=PIPE
    )  # this ensures that ABC is not too verbose, but still prints errors
    # call(["aigtoaig", f.name + ".aig", simplified_filename], stdout=PIPE)

def extract_result(job, output, error, return_value):
    
    seconds, memory = get_benchmark_result(error)
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
    certificate_size = None
    minimized_certificate_size = None
    
    parse_num = re.compile(r"[^\d]*(\d+)")

    for line in output.split(b'\n'):
        line = line.decode()
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
        elif 'Wrote AIG certificate with' in line:
            certificate_size = int(parse_num.match(line).groups(1)[0])
    
    p = {'name' : job,
        'seconds' : seconds,
        'memory' : memory,
        'return_value' : return_value,
        'quantifiers' : quantifiers,
        'existential_variables' : existential_variables,
        'universal_variables' : universal_variables,
        'initial_clauses' : initial_clauses,
        'decisions' : decisions,
        'conflicts' : conflicts,
        'global_conflict_checks' : global_conflict_checks,
        'local_determinicity_checks' : local_determinicity_checks,
        'propagations' : propagations,
        'pure_variables' : pure_variables,
        'propagations_of_constants' : propagations_of_constants,
        'restarts' : restarts,
        'certificate_size' : certificate_size,
        'timeout' : return_value == -15,
        'minimized_certificate_size' : minimized_certificate_size
        }
    return p


def is_failed(expected, result):
    return expected in [10, 20] and result in [10, 20] and result != expected


def read_aig_size(file):
    file.seek(0)
    content = file.read()
    parse_aig_header = re.compile(r"aig \d+ \d+ \d+ \d+ (\d+)")
    parse_num = re.compile(b"[^\\d]*(\\d+)")
    gates_num = int(parse_num.match(content).groups(1)[0])
    return gates_num


def run_job(job, worker_ID, timeout, expected, manage_certificate=False):
    # using 'bash -c' to run the command because otherwise 'sh' may be used on some machines
    if manage_certificate:
        f = tempfile.NamedTemporaryFile(suffix='.aig')
        job = job.format(f.name)

    command = f'bash -c "{TIME_UTIL} {job}"'
    return_value, output, error = call_interruptable(command, timeout)

    if return_value not in [10, 20, 30, -15] or is_failed(expected, return_value):
        log_fail((output + error).decode())
        return None
    else:
        r = extract_result(job, output, error, return_value)
        if manage_certificate and return_value is 10:
            minimize_certificate(f)
            r['minimized_certificate_size'] = read_aig_size(f)
            f.close()
        return r


def worker_loop(job_queue, results, result_queue,
                worker_ID, timeout, manage_certificate=False):
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    while True:
        try:
            # This is hacky; times out after 1 second if no element is in the queue.
            # This terminates the tread!
            (job_name, job, expected) = job_queue.get(block=True,timeout=1)
            r = run_job(job, worker_ID, timeout, expected, 
                        manage_certificate=manage_certificate)
            result_queue.put((job_name, job, expected, r), block=True)

        except queue.Empty:
            break


def run_jobs(jobs, timeout, threads=1, manage_certificate=False):
    global interrupted

    job_queue = mp.Queue()
    result_queue = mp.Queue()  # holds names of jobs that just finished
    results = {}  # holds all results

    for job_name, (job, expected_result) in jobs.items():
        job_queue.put((job_name, job, expected_result))

    workers = []
    for i in range(threads):
        tmp = mp.Process(target=worker_loop, 
                         args=(job_queue, results, result_queue, i, timeout, manage_certificate))
        tmp.start()
        workers.append(tmp)

    FAILEDS = 0
    SUCCESSES = 0
    TIMEOUTS = 0
    UNKNOWNS = 0

    for i in range(len(jobs)):
        try:
            job_name, job, expected, result = result_queue.get(block=True)
            results[job_name] = result
            seconds = None
            memory = None
            return_value = None

            if result is not None:
                seconds = result['seconds']
                memory = result['memory']
                return_value = result['return_value']

            if result is not None and seconds is None:
                log_progress(yellow('TIMEOUT: '))
                TIMEOUTS += 1
            elif return_value == 30:
                log_progress(cyan('UNKNOWN: '))
                UNKNOWNS += 1
            elif return_value == expected or expected == 30 and return_value in [10, 20]:
                log_progress(green('SUCCESS: '))
                SUCCESSES += 1
            else:
                log_progress(red('FAILED:  ') + job_name)
                FAILEDS += 1
            if seconds != None and memory != None:
                log_progress('[{:.2f}s, {:.1f}MB] '.format(seconds, memory))
            log_progress(job_name)
            log_progress('\n')
        except KeyboardInterrupt:
            print('\nTerminating all workers')
            interrupted = True
            for worker in workers:
                worker.terminate()
                worker.join()
            return

    for worker in workers:
        worker.terminate()
        worker.join()

    print('\nStatistics:')
    print(f'Printed {len(jobs)} results in total')

    log_progress(green( 'SUCCESS: ') + "{}\n".format(SUCCESSES))
    log_progress(red(   'FAILED:  ') + "{}\n".format(FAILEDS))
    log_progress(yellow('TIMEOUT: ') + "{}\n".format(TIMEOUTS))
    log_progress(cyan(  'UNKNOWN: ') + "{}\n".format(UNKNOWNS))

    return results


def write_csv(csv_file, results):
    header = ['call', 'result', '"time [s]"',
              '"memory [MB]"', '"certificate size [gates]"',
              '"minimized certificate size [gates]"',
              'restarts', 'conflicts' , 'decisions',
              'propagations', '"pure variables"']
    # with csv_file_name
    csv_file.write(','.join(header) + '\n')

    for name, r in results.items():
        row = [r['name'],
               str(r['return_value']),
               str(r['seconds']),
               str(r['memory']),
               str(r['certificate_size']),
               str(r['minimized_certificate_size']),
               str(r['restarts']),
               str(r['conflicts']),
               str(r['decisions']),
               str(r['propagations']),
               str(r['pure_variables']),
              ]
        csv_file.write(','.join(row) + '\n')


if __name__ == "__main__":
    print('')
    parser = argparse.ArgumentParser()
    parser.add_argument('--timeout', dest='timeout', action='store', type=int, default=10,
                        help='Timeout in seconds (default: 10)')
    parser.add_argument('--csv', dest='csv', action='store', nargs='?', const='tester.csv',
                        metavar='file_name', type=argparse.FileType('w'),
                        help='Write CSV to file (default: tester.csv)')
    parser.add_argument('--threads', dest='threads', action='store', nargs='?', type=int,
                        metavar='num', default=1,
                        help=f'Number of threads to use (default: {1})')  # mp.cpu_count()
    parser.add_argument('--tool', dest='tool', action='store',
                        default='./cadet -v 1',  #  os.path.join(BASE_PATH, './cadet -v 1')
                        help='Define which tool is tested (default "./cadet -v 1").')
    parser.add_argument('-c', '--configs', metavar='C', type=str, nargs='*',
                        dest='configs',
                        default=[''],  # os.path.join(BASE_PATH, './cadet -v 1')
                        help='The list of command line configurations to run'
                        'the tool in. (Default: "")')
    parser.add_argument('-p', '--preprocessor', dest='preprocessor', 
                        action='store', default=None,
                        help='Use this command to set a preprocessor command.')
    parser.add_argument('--minimize_certificates', dest='minimize_certificates', action='store_true',
                        help='Minimize certificates. Use {} in place of certificate file name.')
    parser.add_argument('-d', '--directory', dest='directory', 
                        action='store', default=None,
                        help='Specify folder of formulas to solve.')
    parser.add_argument('-f', '--force', dest='force', 
                        action='store_true', default=None,
                        help='Override CPU load check.')

    instances_file = open('integration-tests/instances.txt', 'r').read()
    all_categories = re.findall(r'\[([A-Za-z0-9_-]+)\]', instances_file)
    for cat in all_categories:
        parser.add_argument(f'--{cat}', dest=cat, action='store_true',
                            help=f'Run the {cat} formulas')

    ARGS = parser.parse_args()

    configs = []
    tool = ARGS.tool
    if ARGS.configs:
        for c in ARGS.configs:
            configs.append(tool + ' ' + c)

    categories = []
    for cat in all_categories:
        if getattr(ARGS, cat):
            if not cat in categories:
                categories.append(cat)

    if not categories and not ARGS.directory:
        parser.print_help()
        exit()

    halt_if_busy(ARGS)

    paths = get_paths_from_categories(categories, ARGS.directory)
    jobs = jobs_from_paths(paths, configs)

    manage_certificate = ARGS.minimize_certificates

    # Run the tests
    results = run_jobs(jobs, ARGS.timeout, ARGS.threads, manage_certificate)

    if ARGS.csv:
        write_csv(ARGS.csv, results)

    if failed:
        sys.exit(1)

    if interrupted:
        print('Interrupted by user')
        sys.exit(1)
