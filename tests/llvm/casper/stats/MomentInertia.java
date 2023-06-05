package original.stats;

/*
    MomentInertia.java
    ==================
    
    A class to calculate the moment of intertia for various situations.
    Copyright (C) 2013  Magdalen Berns
    
    

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


class MomentInertia{
	
	public static double centerUniformRod(double length, double mass){
			return (mass * length * length )/12;  	
	}
	public static double sphere(double length, double mass){
			return (mass * length * length )/12;  	
	}


}