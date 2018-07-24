import sys

c_blue   = '\033[49;0;34m'
c_red    = '\033[49;0;31m'
c_green  = '\033[49;0;32m'
c_cyan   = '\033[49;0;36m'
c_yellow = '\033[49;1;33m'
c_reset  = '\033[0m'

def green(string):
    return c_green + string + c_reset

def red(string):
    return c_red + string + c_reset

def blue(string):
    return c_blue + string + c_reset

def yellow(string):
    return c_yellow + string + c_reset

def cyan(string):
    return c_cyan + string + c_reset

def log(msg):
    print(msg)

def log_progress(msg):
    sys.stdout.write(msg)

def error(msg):
    print(red('Error: ' + msg))

def fatal(msg):
    print(red('Fatal Error: ' + msg))
    exit(1)

