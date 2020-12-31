// MagiC.c

#include "stdio.h"
#include "defs.h"
#include "stdlib.h"
#include "string.h"


#define WAC1 "r1b1k2r/ppppnppp/2n2q2/2b5/3NP3/2P1B3/PP3PPP/RN1QKB1R w KQkq - 0 1"
#define PERFT "q4rk1/2p3pp/1b4n1/pP1p1pP1/3pn3/2P2P1P/1P2Q2K/RNB1R3 w - - 0 23"

int main(int argc, char *argv[]) {

	AllInit();

	S_BOARD pos[1];
    S_SEARCHINFO info[1];
    info->quit = FALSE;
	pos->HashTable->pTable = NULL;
    InitHashTable(pos->HashTable, 64);
	setbuf(stdin, NULL);
    setbuf(stdout, NULL);
    
    int ArgNum = 0;
    
    for(ArgNum = 0; ArgNum < argc; ++ArgNum) {
    	if(strncmp(argv[ArgNum], "NoBook", 6) == 0) {
    		EngineOptions->UseBook = FALSE;
    		printf("Book Off\n");
    	}
    }

	printf("Welcome to MagiC-engine 3.0! Type 'MagiC' for console mode...\n");

	char line[256];
	while (TRUE) {
		memset(&line[0], 0, sizeof(line));

		fflush(stdout);
		if (!fgets(line, 256, stdin))
			continue;
		if (line[0] == '\n')
			continue;
		if (!strncmp(line, "uci",3)) {
			Uci_Loop(pos, info);
			if(info->quit == TRUE) break;
			continue;
		} else if (!strncmp(line, "xboard",6))	{
			XBoard_Loop(pos, info);
			if(info->quit == TRUE) break;
			continue;
		} else if (!strncmp(line, "MagiC",4))	{
			Console_Loop(pos, info);
			if(info->quit == TRUE) break;
			continue;
		} else if(!strncmp(line, "quit",4))	{
			break;
		}
	}

	free(pos->HashTable->pTable);
	CleanPolyBook();
	return 0;
}