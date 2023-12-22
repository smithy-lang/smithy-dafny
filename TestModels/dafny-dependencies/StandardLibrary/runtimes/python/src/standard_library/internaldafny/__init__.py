import sys

internaldafny_dir = '/'.join(__file__.split("/")[:-1])

# extern MUST come first in path
sys.path.append(internaldafny_dir + "/extern")
sys.path.append(internaldafny_dir + "/generated")
