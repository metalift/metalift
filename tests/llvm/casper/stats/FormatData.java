package original.stats;

/**
 * Format Data.java 
 * =============
 * This file is a part of a program which serves as a utility for data analysis
 * of experimental data
 *
 * Copyright (C) 2013-2014  Magdalen Berns <m.berns@sms.ed.ac.uk>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
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

public class FormatData {

    public static void main(String[] args) throws IOException {
	String fileName = IOUtil.getFileName();

	Scanner scan = new Scanner(new BufferedReader(new FileReader("files/"+fileName)));
	PrintWriter fitFout = new PrintWriter("files/data_"+fileName);
      
	int length = IOUtil.skipToInt(scan);

	double xError=IOUtil.skipToDouble(scan);
	double yError= IOUtil.skipToDouble(scan);
	double[][] data = PlotReader.data2Column(scan,length);
	PlotUtil p = new PlotUtil(data);

	PlotWriter.errors(p.x(), p.y(),xError,Calculate.multiply(p.y(),yError), fitFout);
	fitFout.close();
    }
}