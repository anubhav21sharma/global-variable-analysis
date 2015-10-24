BASE_DIR =/home/test/GCC
INSTALL = $(BASE_DIR)/install
CC = $(INSTALL)/bin/g++

PLUGIN_HEADER_FILES= ../include/GlobalVarAnalysis.h ../include/Variable.h ../include/Function.h ../include/Common.h
PLUGIN_SOURCE_FILES= ../src/plugin.cpp ../src/GlobalVarAnalysis.cpp ../src/Variable.cpp ../src/Function.cpp 

GCCPLUGINS_DIR:= $(shell $(CC) -print-file-name=plugin)
INCLUDE= -I$(GCCPLUGINS_DIR)/include -I../include -I$(BASE_DIR)/gcc-4.7.2/gcc -I../src/

PTA_OBJS= Points_to4.o pointstonew2.o parser.o block_information.o con.o cgraph_node.o dataflow.o interval.o

PLUGIN_OBJECT_FILES= plugin.o GlobalVarAnalysis.o Variable.o Function.o

FLAGS= -fPIC -O0 -flto -flto-partition=none #-DPT_STATS -DPT_TIME -DPT_TEST

plugin.o: ../src/plugin.cpp
		$(CC) $(FLAGS) $(INCLUDE) -c $<

GlobalVarAnalysis.o: ../src/GlobalVarAnalysis.cpp ../include/GlobalVarAnalysis.h
		$(CC) $(FLAGS) $(INCLUDE) -c $<
		
Variable.o: ../src/Variable.cpp ../include/Variable.h
		$(CC) $(FLAGS) $(INCLUDE) -c $<
		
Function.o: ../src/Function.cpp ../include/Function.h
		$(CC) $(FLAGS) $(INCLUDE) -c $<

#PTA START
%.o : ../src/%.c
	$(CC) $(FLAGS) $(INCLUDE) -c $< 
%.o : ../src/%.cpp
	$(CC) $(FLAGS) $(INCLUDE) -c $< 
con.o: ../src/con.cpp ../src/con.hpp
	 $(CC) $(FLAGS) $(INCLUDE) -c ../src/con.cpp
block_information.o: ../src/block_information.cpp ../src/block_information.hpp
	$(CC) $(FLAGS) $(INCLUDE) -c ../src/block_information.cpp
cgraph_node.o: ../src/cgraph_node.cpp ../src/cgraph_node.hpp
	$(CC) $(FLAGS) $(INCLUDE) -c ../src/cgraph_node.cpp	
interval.o: ../src/interval.cpp ../src/interval.hpp
	 $(CC) $(FLAGS) $(INCLUDE) -c ../src/interval.cpp
parser.o: ../src/parser.cpp ../src/parser.hpp
	$(CC) $(FLAGS) $(INCLUDE) -c ../src/parser.cpp	
dataflow.o: ../src/dataflow.cpp ../src/dataflow.hpp
	$(CC) $(FLAGS) $(INCLUDE) -c ../src/dataflow.cpp
#PTA END	
	
	

FLAGS= -fPIC -O0 -g3
all:	plugin.so

plugin.so: $(PLUGIN_HEADER_FILES) $(PLUGIN_OBJECT_FILES) $(PTA_OBJS)
	$(CC) $(INCLUDE) $(FLAGS) -shared $^ -o $@

TEST=../TestFiles/test1
test: plugin.so 
	$(CC) -fplugin=./plugin.so $(TEST).c -fdump-ipa-all -O0 -fipa-pta -fno-inline

clean:
	\rm -f plugin.so test *.c.* *~ *.o a.out
