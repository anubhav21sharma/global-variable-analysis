BASE_DIR =/mnt/Acer/GCC
INSTALL = $(BASE_DIR)/install
CC = $(INSTALL)/bin/g++

PLUGIN_SOURCE_FILES= ../src/plugin.cpp

GCCPLUGINS_DIR:= $(shell $(CC) -print-file-name=plugin)
INCLUDE= -I$(GCCPLUGINS_DIR)/include -I../include -I$(BASE_DIR)/gcc-4.7.2/gcc

FLAGS= -fPIC -O2
all:	plugin.so

plugin.so: $(PLUGIN_SOURCE_FILES)
	$(CC) $(INCLUDE) $(FLAGS) -shared $^ -o $@

TEST=../TestFiles/test1
test: plugin.so 
	$(CC) -fplugin=./plugin.so $(TEST).c -fdump-ipa-all -O3 -fipa-pta -fno-inline

clean:
	\rm -f plugin.so test *.c.* *~ *.o a.out
