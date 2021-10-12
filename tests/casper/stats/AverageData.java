package original.stats;

/**
 * AverageData.java 
 * =============
 *		
 * This is a program to help with data analysis.
 * You can open a one column array and average all the data points.
 * File must be in the format where the first line gives its length
 * e.g.
 * length = 30
 * x_1
 * x_2
 * *
 * *
 * *
 * *
 * x + n
 *    
 * Copyright (C) 2013-2014  Magdalen Berns <m.berns@sms.ed.ac.uk>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.

 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
 
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Scanner;

public class AverageData {

    public static void main(String[] args) throws IOException{
      	System.out.printf("Please type the name of the data file you wish to average. \n"); 
    	String choice= IOUtil.getFileName();

    	if ( !choice.equals(null) ) {
        	Scanner scan = new Scanner(new BufferedReader(new FileReader("files/"+choice)));
        	int length = IOUtil.skipToInt(scan);
        	double[] data = PlotReader.data1Column(scan,length);
        	double mean = StatsUtil.mean(data);
        	System.out.printf("Mean value %g \n", mean); 
        	System.out.printf("std Dev value %g \n", Math.sqrt(StatsUtil.variance(data,mean))); 
        	System.exit(0);
        }
    }
}