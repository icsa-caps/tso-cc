TARGET = TSO-CC

MURPHIPATH = ../cmurphi
INCLUDEPATH = ${MURPHIPATH}/include
CFLAGS = -O3

all: ${TARGET}

${TARGET}: ${TARGET}.cpp
	g++ ${CFLAGS} -o ${TARGET} ${TARGET}.cpp -I${INCLUDEPATH}

${TARGET}.cpp: ${TARGET}.m
	${MURPHIPATH}/mu ${TARGET}.m

.PHONY: clean
clean:
	-rm ${TARGET} *.cpp
