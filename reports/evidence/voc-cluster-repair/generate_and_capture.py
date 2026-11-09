"""Run the thesis generator check while retaining exact raw upstream outputs."""
import runpy
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'scripts'))
import table_presentation

original_adapter = table_presentation.adapt_directory

def capture_then_adapt(directory, filenames):
    raw = EVIDENCE / 'tables-raw'
    raw.mkdir(exist_ok=False)
    for name in filenames:
        shutil.copyfile(directory / name, raw / name)
    return original_adapter(directory, filenames)


table_presentation.adapt_directory = capture_then_adapt
sys.argv = [str(ROOT / 'scripts/generate_thesis_tables.py'),
            '--python', sys.executable,
            '--output', str(EVIDENCE / 'tables-final-check'), '--check']
runpy.run_path(sys.argv[0], run_name='__main__')
