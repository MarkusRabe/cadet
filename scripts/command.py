import threading
import subprocess
import traceback
import os, signal

# Source: https://gist.github.com/kirpit/1306188

class Command(object):
    """
    Enables to run subprocess commands in a different thread with TIMEOUT option.

    Based on jcollado's solution:
    http://stackoverflow.com/questions/1191374/subprocess-with-timeout/4825933#4825933
    """
    command = None
    process = None
    status = None
    output, error = '', ''

    def __init__(self, command):
        self.command = command

    def run(self, timeout=None, **kwargs):
        """ Run a command then return: (status, output, error). """
        def target(**kwargs):
            try:
                self.process = subprocess.Popen(self.command, **kwargs)
                self.output, self.error = self.process.communicate()
                self.status = self.process.returncode
            except:
                self.error = traceback.format_exc()
                self.status = -1
        # default stdout and stderr
        if 'stdout' not in kwargs:
            kwargs['stdout'] = subprocess.PIPE
        if 'stderr' not in kwargs:
            kwargs['stderr'] = subprocess.PIPE
        # thread
        thread = threading.Thread(target=target, kwargs=kwargs)
        thread.start()
        try:
            thread.join(timeout)
            if thread.is_alive():
                self.process.terminate()
                os.killpg(self.process.pid, signal.SIGUSR1)
                thread.join()
        except KeyboardInterrupt:
            # make a keyboard interrupt to stop the program
            self.process.terminate()
            os.killpg(self.process.pid, signal.SIGUSR1)
            thread.join()
            raise KeyboardInterrupt
        return self.status, self.output, self.error
        
        
# Calls a program and returns (exit_code, output, error)
def call_interruptable(cmd, timeout=None):
    cmd = Command(cmd)
    return cmd.run(timeout, shell=True, preexec_fn=os.setsid) # http://stackoverflow.com/questions/4789837/how-to-terminate-a-python-subprocess-launched-with-shell-true