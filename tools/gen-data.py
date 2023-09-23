#!/usr/bin/python3
import sys
import getopt

# Input is CSV file with entries in different columns
# Specify columns for X and Y data
# Output is line like the following
#          \addplot coordinates {(4, 900) (8, 8320) (9, 39628) (11, 252970) (12, 1324539) (13, 4095084) (14, 7131764) (15, 15225960)};

# Option: Can also have it draw vertical lines between two points (X,Y) and (X,Y2)


# Threshold value.  Don't include data with Y values exceeding this value
yThresh = 10000 * 1000 * 1000
xThresh = 1000 * 1000 * 1000

# Set any y value below yMin to yMin
yMin = 0.01
xColumn = -1
yColumn = -1
optionString = ""

# For line drawing
y2Column = None

def usage(name):
    print("Usage: %s [-h] ... < file.csv > file.tex")
    print(" -h         Print this message")
    print(" -X XCOL    Set column number to use as X value (counting from 1)")
    print(" -x XTHRESH Set maximum X value included")
    print(" -Y YCOL    Set column number to use as Y value (counting from 1)")
    print(" -y YTHRESH Set maximum Y value included")
    print(" -L YMIN    Set minimum Y value included")
    print(" -2 YCOL2   Set other Y value for line drawing")

    print(" -O OSTRING Specify addplot options (usually quoted string)")

def trim(s):
    while len(s) > 0 and s[-1] in '\r\n':
        s = s[:-1]
    return s

def genPoints(infile, outfile):
    outfile.write("\\addplot %s coordinates {" % optionString)
    for line in infile:
        line = trim(line)
        fields = line.split(",")
        if len(fields) >= max(xColumn,yColumn):
            try:
                fx = float(fields[xColumn-1])
                sx = str(fx)
                if fx > float(xThresh):
                    sys.stderr.write("%f exceeds x threshold %d\n" % (fx, xThresh))
                    continue
            except:
                sx = fields[xColumn-1]
            try:
                fy = max(yMin, float(fields[yColumn-1]))
                sy = str(fy)
                if fy > float(yThresh):
                    continue
            except:
                sy = fields[yColumn-1]
            outfile.write(" (%s,%s)" % (sx, sy))
    outfile.write("};\n")
        
def genLines(infile, outfile):
    for line in infile:
        line = trim(line)
        fields = line.split(",")
        if len(fields) >= max(xColumn,yColumn,y2Column):
            try:
                fx = float(fields[xColumn-1])
                sx = str(fx)
                fy = max(yMin, float(fields[yColumn-1]))
                sy = str(fy)
                fy2 = max(yMin, float(fields[y2Column-1]))
                sy2 = str(fy2)
                if fx > float(xThresh) or fy > float(yThresh) or fy2 > float(yThresh):
                    continue
            except:
                continue
            outfile.write("\\addplot %s coordinates{(%s,%s) (%s,%s)};\n" % (optionString, sx,sy,sx,sy2))

def run(name, args):
    global xThresh, xColumn, yThresh, yColumn, y2Column, yMin, optionString
    optlist, args = getopt.getopt(args, "hx:X:y:Y:2:L:O:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-x':
            try:
                xThresh = float(val)
            except:
                print("Desired x threshold '%s' not a number" % val)
                usage(name)
                return
        elif opt == '-y':
            try:
                yThresh = float(val)
            except:
                print("Desired y threshold '%s' not a number" % val)
                usage(name)
                return
        elif opt == '-L':
            try:
                yMin = float(val)
            except:
                print("Desired y minimum '%s' not a number" % val)
                usage(name)
                return
        elif opt == '-X':
            try:
                xColumn = int(val)
            except:
                print("Desired x column '%s' is not a number" % val)
                usage(name)
                return
        elif opt == '-Y':
            try:
                yColumn = int(val)
            except:
                print("Desired y column '%s' is not a number" % val)
                usage(name)
                return
        elif opt == '-2':
            try:
                y2Column = int(val)
            except:
                print("Desired y2 column '%s' is not a number" % val)
                usage(name)
                return
        elif opt == '-O':
            optionString = val
            if optionString[0] != '[':
                optionString = '[' + optionString
            if optionString[-1] != ']':
                optionString += ']'
        else:
            print("Unknown option '%s'" % opt)
            usage(name)
            return
    if y2Column is None:
        genPoints(sys.stdin, sys.stdout)
    else:
        genLines(sys.stdin, sys.stdout)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
