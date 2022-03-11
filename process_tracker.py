# necessary because Python threads are shut down without any cleanup
from subprocess import Popen
from typing import Any, List

all_processes: List[Popen[Any]] = []
