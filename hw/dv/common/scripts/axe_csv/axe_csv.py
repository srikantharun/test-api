import pandas as pd
import warnings, glob, os
import argparse

class axe_csv(object):
    def __init__(self, verbose=False, max_rows=10, width=240):
        self.df = {}
        self.verbose = verbose
        pd.set_option('display.min_rows',    max_rows)
        pd.set_option('display.max_rows',    max_rows)
        pd.set_option('display.width',       width)

    def read_csv(self, fname, delimiter=','):
        if self.verbose:
            print('Reading CSV file: %s' %(fname))
        self.df[os.path.basename(fname)]         = pd.read_csv(fname, sep=delimiter)
        self.df[os.path.basename(fname)].columns = self.df[os.path.basename(fname)].columns.str.strip() # Remove Leading and Trailing Whitespace
        self.df[os.path.basename(fname)]         = self.df[os.path.basename(fname)].apply(lambda col: col.apply(self.convert_to_numeric))
        self.df[os.path.basename(fname)]         = self.df[os.path.basename(fname)].dropna(how='all')

    def convert_to_numeric(self, value):
        try:
            return pd.to_numeric(value)
        except (ValueError, TypeError):
            return value

    def combine(self):
        if self.verbose:
            print('Combining CSV files')
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", FutureWarning)
            self.df['combined'] = pd.concat([self.df[f] for f in self.df], axis=0, join='outer')
        self.df['combined'].drop_duplicates()
        self.df['combined'] = self.df['combined'].fillna('')
        self.df['combined'].reset_index(drop=True)

    def sort(self, column):
        if self.verbose:
            print('Sorting combined dataframe by %s' %(column))
        self.df['combined'] = self.df['combined'].sort_values([column], ascending=[True])

    def query(self, query=None):
        if self.verbose:
            print('Querying combined dataframe')
        if query is None:
            return self.df['combined']
        else:
            return self.df['combined'].query(query)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Analyze AXE CSV Files')
    parser.add_argument('--icsv',               default='*.csv',     help='Input global to find src csvs (default="*.csv")')
    parser.add_argument('--ocsv',               default=None,        help='Output CSV file')
    parser.add_argument('--otxt',               default=None,        help='Output TXT file')
    parser.add_argument('--verbose',            action='store_true', help='Verbose output')
    parser.add_argument('--nostdout',           action='store_true', help='Suppress standard output')
    parser.add_argument('--delimiter',          default=',',         help='CSV delimiter (default:,)')
    parser.add_argument('--sort',               default=None,        help='Sort / order by')
    parser.add_argument('--query',              default=None,        help='Query to apply to data')
    parser.add_argument('--width',              default=240,         help='Display width')
    parser.add_argument('--max_rows', type=int, default=None,        help='Maxium number of rows to display (default=all)')

    # Parse the arguments
    args = parser.parse_args()

    # Create the class
    csv = axe_csv(verbose=args.verbose, max_rows=args.max_rows, width=args.width)

    # Find all files
    for c in glob.glob(args.icsv):
        csv.read_csv(c, args.delimiter)

    # Combine
    csv.combine()

    # Sort
    if args.sort is not None:
        csv.sort(args.sort)

    # Query
    rsp = csv.query(args.query)

    # Output
    if args.ocsv is not None:
        rsp.to_csv(args.ocsv, index=False)

    if args.otxt is not None:
        with open(args.otxt, 'w') as f:
            f.write(rsp.to_string(index=False))

    if not args.nostdout:
        print(rsp)
