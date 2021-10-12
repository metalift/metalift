package original.stats;

/*
		ExtractColumn.java 
		=============
		
    This is a java program to be run when you want to pull a column out of a data file 
    in order to meddle with it. Copyright (C) 2013  Magdalen Berns

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
 
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Scanner;

public class ExtractColumn {

	public static void main(String[] args) throws IOException {
     			
		System.out.printf("Which file would you like to pull a column out of? \n"); 
		String inFileName = IOUtil.getFileName();
	 	if(inFileName.equals("!")){
 		 	System.out.println("No file selected.");
  		}
  		else{

			Scanner scan = new Scanner(new BufferedReader(new FileReader("files/"+inFileName)));
			PrintWriter outFile = new PrintWriter("column.txt");
  			int length = IOUtil.skipToInt(scan);
			double xError=IOUtil.skipToDouble(scan);
			double yError= IOUtil.skipToDouble(scan);    
   			double[][] data = PlotReader.data2Column(scan,length);
   			PlotUtil p = new PlotUtil(data);

			PlotWriter.aColumn(p.y(),outFile);
			outFile.close();
 	 	} 
	}  
}