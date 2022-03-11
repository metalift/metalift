from __future__ import annotations

# necessary because Python threads are shut down without any cleanup
from subprocess import Popen
from typing import List

all_processes: List[Popen[bytes]] = []
