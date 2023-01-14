/*========================================================================
  Copyright (c) 2022, 2023 Randal E. Bryant, Carnegie Mellon University
  
  Permission is hereby granted, free of charge, to any person
  obtaining a copy of this software and associated documentation files
  (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software,
  and to permit persons to whom the Software is furnished to do so,
  subject to the following conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
  ========================================================================*/

// Turn POG assertions into LRAT
//#define LRAT


#include <string.h>
#include <stdlib.h>
#include "report.h"
#include "ilist.h"
#include "writer.hh"

/// Generic Writer

Writer::Writer(const char *fname) {
    file_name = (char *) malloc(strlen(fname)+1);
    strcpy(file_name, fname);
    line_count = 0;
    outfile = fopen(file_name, "w");
    if (outfile == NULL) {
	err(false, "Couldn't open output file '%s'\n", fname);
    }
}

Writer::Writer() {
    file_name = NULL;
    line_count = 0;
    outfile = stdout;
}

void Writer::enable_comments() {
    do_comments = true;
}

void Writer::comment(const char *fmt, ...) {
    if (!do_comments)
	return;
    va_list ap;
    va_start(ap, fmt);
    fprintf(outfile, "c ");
    vfprintf(outfile, fmt, ap);
    fprintf(outfile, "\n");
    line_count++;
    fflush(outfile);
    va_end(ap);
}

void Writer::write_text(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(outfile, fmt, ap);
    va_end(ap);
}

void Writer::start_line() {
}

void Writer::add_int(int v) {
    write_text("%d ", v);
}
void Writer::add_text(const char *txt) {
    write_text("%s", txt);
}

void Writer::write_list(ilist vals) {
    start_line();
    for (int i = 0; i < ilist_length(vals); i++)
	add_int(vals[i]);
    add_int(0);
}

void Writer::comment_list(ilist vals) {
    if (!do_comments)
	return;
    fprintf(outfile, "c ");
    for (int i = 0; i < ilist_length(vals); i++)
	add_int(vals[i]);
    add_int(0);
    fprintf(outfile, "\n");
}

void Writer::finish_line(const char *txt) {
    write_text("%s\n", txt);
    line_count++;
}

void Writer::finish_file() {
    if (outfile != stdout)
	fclose(outfile);
    outfile = NULL;
    if (file_name == NULL)
	report(1, "%d lines written\n", line_count);
    else
	report(1, "File %s.  %d lines written\n", file_name, line_count);
}

/// Writing CNF files
CnfWriter::CnfWriter() : Writer() {}
CnfWriter::CnfWriter(const char *fname) : Writer(fname) {}

void CnfWriter::write_header(int nv, int nc) {
    write_text("p cnf %d %d", nv, nc);
    finish_line("");
}

PogWriter::PogWriter() : Writer() {}
PogWriter::PogWriter(const char *fname) : Writer(fname) {}

void PogWriter::start_assertion(int cid) {
#ifdef LRAT
    write_text("%d ", cid);
#else
    write_text("%d a ", cid);
#endif
}

void PogWriter::start_and(int cid, int var) {
    write_text("%d p %d ", cid, var);
}

void PogWriter::start_or(int cid, int var) {
    write_text("%d s %d ", cid, var);
}

void PogWriter::start_clause_deletion(int cid) {
    write_text("dc %d ", cid);
}

void PogWriter::operation_deletion(int var) {
    write_text("do %d", var);
    finish_line("");
}

void PogWriter::constant(int cid, int val) {
    write_text("%d k %d", cid, val);
    finish_line("");
}
