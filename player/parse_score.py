import os
import re

OUTFILE = ".output"
REGEX = "depth (?P<depth>\d+) .* \(microsec\) (?P<time>\d+) nodes"


def _us_to_ms(time):
  time = int(time)
  return time / 1000.


def parse(outfile):
  with open(outfile) as f:
    data = {}
    for line in f:
      match = re.findall(REGEX, line)
      if len(match) == 1:
        depth, time = match[0]
        data[depth] = _us_to_ms(time)
    return data


def pprint(data):
  print "depth\ttime (millisec)"
  for k, v in data.iteritems():
    print "%s\t%s" % (k, v)


def cleanup(outfile):
  try:
    os.remove(outfile)
  except OSError:
    pass


def process_output(outfile):
  data = parse(outfile)
  pprint(data)
  cleanup(outfile)

if __name__ == "__main__":
  import sys
  if len(sys.argv) == 2:
    outfile = sys.argv[1]
  else:
    outfile = OUTFILE
  process_output(outfile)
