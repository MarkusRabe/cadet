#!/usr/bin/env python

import argparse, csv

def convert(csv_file, dat_file):
    csvreader = csv.reader(csv_file, delimiter=',')

    column = None
    data = []
    for i, row in enumerate(csvreader):
        if i is 0:
            # identify column
            for i, column_name in enumerate(row):
                print(column_name)
                if 'time' in column_name:
                    column = int(i)
                    break;
        else:
            if row[column] != 'None':
                data.append(float(row[column]))

    print(f'Found {len(data)} non-None items')

    data.sort()

    for i, t in enumerate(data):
        dat_file.write(f'{i+1}\t{t}\n')

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('csv', metavar='csv_file', type=argparse.FileType('r'), help='CSV file')
    parser.add_argument('dat', metavar='dat_file', type=argparse.FileType('w'), help='Output file in dat format')
    
    args = parser.parse_args()
    
    convert(args.csv, args.dat)
    