#!/Library/Frameworks/Python.framework/Versions/3.4/bin/python3.4
__author__ = 'Robert Battocletti'
__co_author__ = 'Amy Battocletti'
__email__ = 'batto28@gmail.com'
'''
Has previously been named "Pyne" and "Pyne_jp" in the github folder.  This file
name changed to "Battocletti_Sved_implementation" for easier identification.

The purpose of this program is to estimate population effective population size 
(Ne) using microsatellite genotype data. It implements the methods presented in 
Sved et al. 2013, most notably, r^comp and the permutation correction factor.  

Full citation for Sved et al. 2013:

Sved JA, Cameron EC, and AS Gilchrist. 2013. Estimating effective population 
size from linkage disequilibrium between unlinked loci: Theory and application 
to fruit fly outbreak populations.  PLOS One 8(7): e69078.

'''

#The cgi library provides access to a standard environment for web servers to interface with executable programs.
import cgi
#The wsgiref library provide web server functionality which enables the cross platform interface.
from wsgiref.simple_server import make_server
#The threading library enables the application to conduct several functions independent of each other.
from threading import Thread as thread
#The time library provides several builtin functions time conversions and other functionality for methods dependent on time.
from time import localtime,sleep
#The collections library OrderedDict module provides more dictionary functionality than the standard dictionary collection.
from collections import OrderedDict
#The web browser library allows your to access the systems default web browser. This is required for the cross platform interface.
from webbrowser import open_new as web
#The os library allows you to access to interact with the system's operating system.
import os
import re
# The collections library Counter module grants access to functions to compare and combine data structures.
from collections import Counter
#The itertools library product module provides pre-built product functions.
from itertools import product, combinations
#The Decimal library provides more precision than type float.
from decimal import *
#The statistics library provides basic stat functions.
import statistics
#The random library allows you greater control of the random seed.
import random
#The math library provides general math functionality.
import math
#The scipy library is a module that provides complex mathematical functionality.
from scipy import stats
#import scipy.special as stats
from fnmatch import fnmatch
import copy

class thread_share():
    '''
    Instances of class thread_share are used to share and store variables/collection across multiple threads.
    '''
    def __init__(self):
        self.args = OrderedDict()
        self.counter = 0
        self.status = '0'
        self.sub_status = '0'
        self.port = 8201
        self.composite_haplotype_tables_r_squared = []
        self.jack_knife = []
        self.loci_num = 0
        self.final_results = []
        self.number_of_populations = 0
        self.current_population_index = 0
        self.r2_permute_final_results = []
        self.population_name = ""
        self.confidence_interval = {}
        self.alleles_below_threshold_by_locus = []
        self.program_status_dict = {'0':["Not running", "black"],
                               '1':["Processing data file ", "red"],
                               '2':["Processing complete", "black"],
                               '3':["Finished processing waiting for a new file", "black"],
                               '4':["No more files to process, closing the program", "black"]}
        self.program_sub_status_dict = {'0':['Waiting for configuration','blue'],
                                        '1':['Parsing csv data file','yellow'],
                                        '11':['Parsing popgene data file','yellow'],
                                        '2':['building permutes for ','yellow'],
                                        '3':['Generating haplotype tables for ','yellow'],
                                        '4':["Reading configuration","yellow"],
                                        '5':["Calculating Jackknife for ","yellow"],
                                        '6':["Calculating Permutes for ","yellow"],
                                        '7':["Outputting your results for ","yellow"],
                                        '8':["Your results for have been written to your output file ", "black"],
                                        '9':["Building Jackknifes for ","yellow"],
                                        '10':["Building permutes for ","yellow"]
                                        }
        self.order = OrderedDict({'parametric_lower_CI': '', 'parametric_upper_CI': '', 'Ne': ''})
        self.order_list = ('Ne', 'parametric_upper_CI', 'parametric_lower_CI')
        self.date = ""
        self.date_good = True
        self.report_builder_store = ""
        self.datasheets = []
        self.permute_corrections = OrderedDict()
        self.cd_controller = ("r^Comp","r^Delta")
        self.permute_controller = ("_permute_corrected_Ne",
                                   "_permutation_correction_factor",
                                   "_permute_corrected_upper_Ne",
                                   "_permute_corrected_lower_Ne",
                                   "_permute_corrected",
                                   "_permute_corrected_upper",
                                   "_permute_corrected_lower",
                                   )
        self.permute_jk_controller = ("permute upper", "permute lower")

    def datetime_update(self):
        self.date = "_{:02}{:02}{:02}_{:02}{:02}".format(localtime().tm_year,
                                                         localtime().tm_mon,
                                                         localtime().tm_mday,
                                                         localtime().tm_hour,
                                                         localtime().tm_min)
    def program_sub_status(self):
        if self.sub_status is not '1':
            return ["{}{}".format(self.program_sub_status_dict[self.sub_status][0], self.population_name), self.program_sub_status_dict[self.sub_status][1]]
        else:
            return ["{}{}".format(self.program_sub_status_dict[self.sub_status][0], self.args['Input_File']), self.program_sub_status_dict[self.sub_status][1]]
    def program_status(self):
        if self.status is "1":
            return ["{}{}".format(self.program_status_dict[self.status][0], self.args['Input_File']), self.program_status_dict[self.status][1]]
        else:
            return self.program_status_dict[self.status]
    def reset_status(self):
        self.sub_status =  '0'
        self.status = '0'
'''
this is a global exec an instances of thread_share.
'''
t_share = thread_share()

####Start functions that define and execute a web server and user interface####

def build_header(tag):
    '''
    This function returns html/css header data to the web server that is used to format the interface.
    '''
    global t_share
    if tag == 0:
        return '''
<!DOCTYPE html>
<html>
  <meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
  {}
'''.format(r'<meta http-equiv="refresh" content="3" />' if t_share.status == '1' else "")

    elif tag == 1:
        return '''
  <style>
  #header {
           background:#ff0;
           padding:10px;
           background:white
           }
  #body1 {
         padding:10px;
         padding-bottom:60px;
         background:lightgrey
         }

  #cssTable01 td {
                  text-align:center;
                  vertical-align:middle;
                  border: 1px solid black;
                  border-collapse: collapse;
                  bgcolor: white;
                  }

  #footer {
            position:absolute;
            bottom:0;
            width:100%;
            height:100px;
            background:white;
            }
  </style>
'''

def build_report01():
    #This function is used to return data in a table row.
    global t_share
    str_return00 = '''
   <table border="1" id="cssTable01" width="100%">
'''
    str_return01 = '''
    <tr><th>{}</th><th>Ne</th><th>parametric_upper_CI</th><th>parametric_lower_CI</th>
'''.format(t_share.population_name)
    for result in t_share.final_results:
        var1 = ""
        var2 = ""
        for keys in result.keys():
            for key1 in list(result.keys()):
                if "S" in key1:
                    var1 = key1
                elif "r^" in key1:
                    var2 = key1
        str_return01 += '''
     <tr><td><b>Ne based on {} using {}</b></td>
'''.format(var1, var2)
        for ordered_key in t_share.order_list:
            for tmp_key in result:
                if ordered_key in tmp_key:
                    var3 = tmp_key
                    str_return01 += '''
    <td>{:.5}</td>'''.format(result[var3])
                    continue
        str_return01 += '''
    </tr>'''
    str_return01 += '''
   </table>
'''
    t_share.report_builder_store += "\n" + str_return00 + str_return01 + "\n"
    return True

def build_body():
    '''
    This function is the user interface and provides default variables.
    '''
    global t_share
    return '''
                    <div id="header">
                      <hr>
                      <h1 style="text-align: center;">Effective Population Size</h1>
                      <hr> </div>
                    <div id="body1">
                      <form method="post"><br>
                        <br>
                        <hr>
                        <center>
                          <h3 style="color:black">Working Folder :: {}</h3>
                        </center>
                        <hr>
                        <table style="width: 874px; height: 80px;" align="center">
                          <tbody>
                            <tr>
                              <td style="width: 200px; text-align: right;"><b>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
Input
                                  File&nbsp;<span style="font-family: Lucida Grande;">&nbsp;</span>
                                </b></td>
                              <td style="text-align: left;">&nbsp;Place your
                                data files in the Input_datafiles folder located
                                under PyNe.<br>
                              </td>
                              <td style="vertical-align: top; text-align: center;"><br>
                              </td>
                            </tr>
                            <tr>
                              <td style="text-align: right;"><b>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;
Output
                                  Directory&nbsp; </b><br>
                                <b> </b></td>
                              <td style="text-align: left;">&nbsp;Result files
                                will be located in the results folder located
                                under PyNe.<br>
                              </td>
                              <td style="vertical-align: top; text-align: center;"><br>
                              </td>
                            </tr>
                          </tbody>
                        </table>
                        <hr>
                        <table style="width: 874px; height: 40px;" align="center">
                          <tbody>
                            <tr>
                              <td><br>
                              </td>
                            </tr>
                            <tr>
                              <td style="text-align: left;" colspan="3"><b>Configuration Settings</b></td>
                            </tr>
                            <tr>
                              <td style="width: 5%"><br>
                              </td>
                              <td style="text-align: left; width:27%;"><b>Set
                                  alpha level for all intervals </b></td>
                              <td><input name="alpha" value="{}"></td>
                            </tr>
                          </tbody>
                        </table>
                        <table style="width: 874px; height: 45px;" align="center">
                          <tbody>
                          </tbody>
                          <tbody>
                            <tr>
                              <td style="text-align: center; width: 5%"><input name="Use_threshold"
                                  value=True {}=""
                                  type="checkbox">
                              </td>
                              <td style="text-align: left;" colspan="3"><b>Use
                                  minimum allele frequency threshold<br>
                                </b></td>
                            </tr>
                            <tr>
                              <td style="width: 5%"><br>
                              </td>
                              <td style="width: 5%"><br>
                              </td>
                              <td style="width: 22%"><b>Minimum allele frequency<br>
                                </b></td>
                              <td><input name="Threshold" value="{}"></td>
                              <td style="vertical-align: top;"><br>
                              </td>
                            </tr>
                          </tbody>
                        </table>
                        <table style="width: 874px; height: 45px;" align="center">
                          <tbody>
                          </tbody>
                          <tbody>
                            <tr>
                              <td style="text-align: center; width: 5%"><input name="Use_Permute"
                                  value="True"
                                  {}=""
                                  type="checkbox">
                              </td>
                              <td style="text-align: left;" colspan="3"><b>Use
                                  permutation correction factor<br>
                                </b></td>
                            </tr>
                            <tr>
                              <td style="width: 5%"><br>
                              </td>
                              <td style="width: 5%"><br>
                              </td>
                              <td style="width: 22%"><b>Number of permutations<br>
                                </b></td>
                              <td><input name="permute_number" value="{}"></td>
                              <td style="vertical-align: top;"><br>
                              </td>
                            </tr>
                          </tbody>
                        </table>
                        <table style="width: 874px; height: 30px;" align="center">
                          <tbody>
                            <tr>
                              <td style="text-align: center; width: 5%;"><input
                                  name="Use_Jackknife"
                                  value="True"
                                  {}=""
                                  type="checkbox"></td>
                              <td><b>Produce delete-one locus-pair jackknife
                                  confidence intervals</b></td>
                            </tr>
                          </tbody>
                        </table>
                        <table style="width: 874px; height: 30px;" align="center">
                          <tbody>
                            <tr>
                              <td style="text-align: center; width: 5%;"><input
                                  name="Use_Median"
                                  value="True"
                                  {}=""
                                  type="checkbox"></td>
                              <td><b>Use Median instead of Mean for Correction Factor</b></td>
                            </tr>
                          </tbody>
                        </table>
                        <table style="width: 874px; height: 35px;" align="center">
                          <tbody>
                            <tr>
                              <td style="text-align: center; width: 5%;"><input
                                  name="Export_Htlm_Report"
                                  value="True"
                                  {}=""
                                  type="checkbox"></td>
                              <td><b>Generate htlm Report</b></td>
                            </tr>
                            <tr>
                              <td><br>
                              </td>
                              <td style="text-align: center;" colspan="2"><input
value="Start Processing"
action=""
type="submit"></td>
<td>
<br></td>
</tr>
<tr>
</tr>
</tbody>
   </table>
   <hr>
   <center><h3 style=\"color:{}\">STATUS :: {}</h3></center>
   <center><h4 style=\"color:{}\">{}</h4></center>
   <center><h4 style=\"color:{}\">{}</h4></center>
   <hr>
</form>
'''.format(os.path.realpath("./PyNE"),
           t_share.args.get('alpha', '0.05'),
           "{}".format('checked' if t_share.args.get('Use_threshold','False') == 'True' else 'checked'),
           t_share.args.get('Threshold','0.0'),
           "{}".format('checked' if t_share.args.get('Use_Permute','False') == 'True' else 'checked'),
           t_share.args.get('permute_number','5'),
           "{}".format('checked' if t_share.args.get('Use_Jackknife','False') == 'True' else 'checked'),
           "{}".format('checked' if t_share.args.get('Use_Median', 'False') == 'True' else 'unchecked'),
           "{}".format('checked' if t_share.args.get('Use_missing_data','False') == 'True' else 'unchecked'),
           "{}".format('checked' if t_share.args.get('Export_Htlm_Report','False') == 'True' else 'unchecked'),
           "{}".format(t_share.program_status()[0]),
           "{}".format(t_share.program_status()[1]),
           "{}".format(t_share.program_sub_status()[0]),
           "{}".format(t_share.program_sub_status()[1]),
           "{}".format("Processing population {} of {}".format(t_share.current_population_index +1, t_share.number_of_populations) if t_share.status is '1' else ""))

def build_footer():
    '''
    this function returns the html footer for the user interface webpage.
    '''
    return '''
  <div>
   <address style="text-align:center">
   Robert Battocletti
   batto28@gmail.com
   </address>
  </div>
</html>
'''

def report_builder():
     '''
     This function is used to call and format the outputs from build_report01 and build_report02.
     '''
     global t_share
     return '''
 {}
 '''.format(t_share.report_builder_store)

def build_form():
    '''
    This function is used to combine the functions that define the user interface.
    '''
    global t_share
    return "{}{}{}{}{}".format(build_header(0),
                               build_header(1),
                               build_body(),
                               report_builder() if t_share.status == '2' and t_share.args.get('Export_Htlm_Report', 'False') == 'True' else "</div>",
                               build_footer())

def build_args(post):
    '''
    This function is used to process the parameters defined by the user via the webpage interface.
    '''
    global t_share
    tmp_args = OrderedDict()
    t_share.status = '1'
    t_share.sub_status = '4'
    for item in post:
        if item.name == "Input_File":
            tmp_args[item.name] = item.value.replace("file://","").replace("%20"," ")
        elif item.name == 'alpha':
            tmp_args[item.name] = float(item.value)
        elif item.name == 'Threshold':
            for spec_item in post:
                if spec_item.name == 'Use_threshold':
                    tmp_args[item.name] = Decimal(item.value) if spec_item.value == 'True' else Decimal(0)
        elif item.name == 'permute_number':
            for spec_item in post:
                if spec_item.name == 'Use_Permute':
                    tmp_args[item.name] = int(item.value) if spec_item.value == 'True' else int(0)
        else:
            tmp_args[item.name] = item.value
    return tmp_args

def web_client(port):
    '''
    This function is used to launch the clients default webserver and call the web user interface.
    '''
    sleep(2)
    web("http://localhost:{}".format(port))

def app(environ, start_response):
    '''
    This function provides the primary loop for the webserver used to control the processing of user arguments and
    building of the webpage during requests.
    Note: this is controlled by line 3 of server daemon.
    '''
    global t_share
    if environ['REQUEST_METHOD'] == 'POST' and t_share.status == '0' or t_share.status == '4':
        post_env = environ.copy()
        post_env['QUERY_STRING'] = ''
        post = cgi.FieldStorage(
            fp=environ['wsgi.input'],
            environ=post_env,
            keep_blank_values=True)
        tmp_args = build_args(post.list)
        if t_share.args != tmp_args:
             t_share.args = tmp_args
             sleep(1)
    start_response('200 OK', [('Content-Type', 'text/html')])
    return [bytes(build_form(), 'utf-8')]

def server_daemon():
    '''
    This function is used to start the webserver and call the master loop(app).
    '''
    global t_share
    try:
        httpd = make_server('', t_share.port, app)
        httpd.serve_forever()
    except KeyboardInterrupt:
        print('Goodbye.')

####End webserver and interface functions####

def system_alerts():
    '''
    This function is used to generate an user space alert on all platforms given an exception event.
    '''
    os.system('zenity --info --text="Stuff"')

def process_input_file(file_name):
    '''
    :function process_input_file
        This function forward the input file into the proper function for its file type.
            csv = input_dataset_csv(file_name)
            popgene = input_dataset_popgene(file_name)
    :param
        file_name variable t_share.args['Input_File'] derived from user input.
    :raises
        No exceptions are expected in this function
    :returns
        See the return the output from input_dataset_csv or input_dataset_popgene depending on file type.
    '''
    global t_share
    confidence_interval_limits()
    if "csv" in file_name:
        t_share.sub_status = '1'
        return input_dataset_csv(file_name)
    else:
        t_share.sub_status = '11'
        return input_dataset_popgene(file_name)

def confidence_interval_limits():
    global t_share
    t_share.confidence_interval['lower_limit'] = round(int(t_share.args.get('permute_number','0')) * (t_share.args['alpha'] / 2))
    t_share.confidence_interval['upper_limit'] = round(int(t_share.args.get('permute_number','0')) * (1 - (t_share.args['alpha'] / 2)))
    t_share.confidence_interval['median'] = round((t_share.confidence_interval['upper_limit'] - t_share.confidence_interval['lower_limit'])/2)

def input_dataset_csv(file_name):
    '''
    :function input_dataset_csv
        This function will process data formatted as a csv.
        #1 = Since the file is input as a csv, this tells the program to break each row into separate values at the
        commas, forming columns. As a result, each row represents an individual and each column represents an allele.
        alleles = []  #This initializes the list called "alleles".
        #2 = Stores the individuals genotypes by locus. Each locus is a column and each individual is a row
        #3 = Cycle through each locus to format and store the genotypes in this format '3,4'
        #4 = Store the number of individuals  in a global variable for later use.
    :param
        -file_name variable t_share.args['Input_File'] derived from user input.
        -example:
            02,02,07,00,08,08,04,06,02,09,10,11,03,04,09,09,06,06
            04,06,09,12,08,08,04,04,09,11,08,09,04,05,09,09,06,08
            04,04,10,10,08,11,04,04,03,03,06,08,04,05,09,09,08,10
            02,03,10,10,08,10,04,05,05,08,09,09,04,05,09,10,06,08
    :raises
        function will raise exception if the input file does not exist.
    :returns
        returns a list of one population with nested lists for genotypes by locus. This means that each item in the
        population list is a locus (for example, 9 loci equals 9 items), and within each of those items is a nested
        list that contains the genotypes for individuals 0 through n (for example, if there are 30 individuals, then
        there will be thirty genotypes within each nested list).
        *NOTE: This examples will be multiplied by the number of permutes requested. Index0 will always contain the
               original data.
            -example
                [[[locus0 genotypes],[locus1 genotypes],[locus2 genotypes],[locus3 genotypes][locus4 genotypes],...],]
                [['2,2','4,6','4,4','2,3'],['7,0','9,12','10,10','10,10'],...]
    '''
    global t_share
    processed_input_datafile = []
    current_population_dictionary = {}
    csv_processing_1 = [line.split(',') for line in open(r'{}'.format(file_name)).read().splitlines()] #1
    t_share.alleles_below_threshold_by_locus = threshold_filter(csv_processing_1)
    genotype_by_locus = [] #2
    for locus_num in range(0, len(csv_processing_1[0]), 2): #3
        locus_genotypes = ["{},{}".format(int(individual[locus_num]), int(individual[locus_num+1])) for individual in csv_processing_1]#3
        genotype_by_locus.append(locus_genotypes)#3
    t_share.sub_status = '2'
    input_plus_permutes = permutes(genotype_by_locus)
    current_population_dictionary['dataset'] = input_plus_permutes
    processed_input_datafile.append(current_population_dictionary)
    return processed_input_datafile

def input_dataset_popgene_helper(current_population, population_name ):
    current_population_dictionary = {}
    popgene_processing_1 = [line for line in current_population if line]
    current_population_dictionary[population_name] = popgene_processing_1
    return current_population_dictionary

def input_dataset_popgene(file_name):
    '''
    :function
        This function will process populations formatted as a gen_pop.
    :param
        -file_name variable t_share.args['Input_File'] derived from user input.
        -example:
            Test_Pop_100_everything
            Locus_1
            Locus_2
            POP
            all_data, 13 16 21 21
            all_data, 13 16 21 21
            all_data, 16 13 21 24
            all_data, 16 13 21 24
    :raises
        function will raise exception if the input file does not exist.
    :returns
        returns a list of Ordered dictionaries with populations linked nested lists for genotypes by locus. This means that each item in the
        population list is a locus (for example, 9 loci equals 9 items), and within each of those items is a nested
        list that contains the genotypes for individuals 0 through n (for example, if there are 30 individuals, then
        there will be thirty genotypes within each nested list).
        *NOTE: This examples will be multiplied by the number of permutes requested. Index0 will always contain the
               original data.
            -example
                [{'pop1' :[[locus0 genotypes],[locus1 genotypes]]},{'pop2': [[locus0],[locus1]]} ]
                [{'all_data':['13,16', '13,16', '16,13', '16,13],['21,21', '21,21', '21,24', '21,24']}...]
    '''
    global t_share
    processed_input_datafile = []
    current_population = []
    current_population_dictionary = {}
    population_name_set = False
    for line in open(file_name):
        if line.lower().strip().split(" ")[0] == "pop":
            population_name_set = True
            if len(line.rstrip().split(" ")) > 1:
                population_name = line.rstrip().split(" ")[1].replace(",","")
            elif len(current_population) > 0:
                processed_input_datafile.append(input_dataset_popgene_helper( current_population, population_name ))
                del population_name; current_population = []; current_population_dictionary = {}
        else:
            try:
                if population_name_set:
                    population_name
                    current_population.append(line.rstrip().split(" ")[1:])
            except NameError:
                population_name = line.rstrip().split(" ")[0]
                if population_name_set:
                    current_population.append(line.rstrip().split(" ")[1:])
                else:
                    continue
    processed_input_datafile.append(input_dataset_popgene_helper( current_population, population_name ))
    population_stats(processed_input_datafile)
    del current_population, current_population_dictionary, population_name
    for population in processed_input_datafile:
        for population_name in population:
            popualtion_pre_filter = []
            for individual in population[population_name]:
                individual_pre_filter = []
                for locus in individual:
                    alsz = int(len(locus)/2)
                    individual_pre_filter.append(locus[:alsz])
                    individual_pre_filter.append(locus[-alsz:])
                popualtion_pre_filter.append(individual_pre_filter)
        t_share.alleles_below_threshold_by_locus = threshold_filter(popualtion_pre_filter)
        genotype_by_locus = []
        for locus_num in range(0, len(popualtion_pre_filter[0]) -1,2):  # 3
            locus_genotypes = ["{},{}".format(int(individual[locus_num]), int(individual[locus_num + 1])) for individual in
                               popualtion_pre_filter]  # 3
            genotype_by_locus.append(locus_genotypes)  # 3
        population[population_name] = permutes(genotype_by_locus)
    return processed_input_datafile

def population_stats(processed_input_datafile):
    population_collections = OrderedDict()
    population_stat_collection = OrderedDict()
    for population in processed_input_datafile:
        for population_name, population_loci in population.items():
            population_collections[population_name] = OrderedDict()
            population_stat_collection[population_name] = OrderedDict()
            for locus in population_loci:
                for locus_index, genotype in enumerate(locus):
                    if not population_collections[population_name].get(str(locus_index), False):
                        population_collections[population_name][str(locus_index)] = []
                        population_stat_collection[population_name][str(locus_index)] = []
                    population_collections[population_name][str(locus_index)].append(genotype[:2])
                    population_collections[population_name][str(locus_index)].append(genotype[-2:])
                    population_stat_collection[population_name][str(locus_index)].append("{},{}".format(genotype[:2], genotype[-2:]))
    del population
    for population_name in population_collections.keys():
        for locus_index, locus_alleles in population_collections[population_name].items():
            population_collections[population_name][locus_index].append(Counter(locus_alleles))
            population_stat_collection[population_name][locus_index].append(population_collections[population_name][locus_index][-1])
            if population_stat_collection[population_name][locus_index][-1].get('00', False):
                del population_stat_collection[population_name][locus_index][-1]['00']
    with open("{}/{}_population_stats01.csv".format(t_share.args['output_Directory'], t_share.args["Input_File"].split("/")[-1]), "x") as result_file:
        result_file.write("Population Name"); controller = False
        for population_name in population_collections.keys():
            if not controller:
                for locus_num in range(1,len(population_collections[population_name])+1):
                    result_file.write(",A{}".format(locus_num))
                    controller = True
            result_file.write("\n{}".format(population_name.strip(",")))
            for locus_id, allele_collection in population_collections[population_name].items():
                if locus_id == str(len(population_collections[population_name].keys())):
                    result_file.write("\n")
                if allele_collection[-1].get('00', False):
                    del allele_collection[-1]['00']
                result_file.write(",{}".format(len(allele_collection[-1].keys())))
        population_names = list(population_collections.keys())
        enrichment_all_populations = population_collections[population_names[0]]
        for k in enrichment_all_populations.keys():
            del enrichment_all_populations[k][-1]
        for population_index in range(1,len(population_names)):
            for pop_key in enrichment_all_populations.keys():
                del population_collections[population_names[population_index]][pop_key][-1]
                enrichment_all_populations[pop_key].extend(population_collections[population_names[population_index]][pop_key])
        result_file.write("\nTotal Richness")
        for k,v in enrichment_all_populations.items():
            enrichment_all_populations[k] = Counter(v)
            if enrichment_all_populations[k].get('00', False):
                del enrichment_all_populations[k]['00']
            result_file.write(",{}".format(len(enrichment_all_populations[k])))
    with open("{}/{}_population_stats02.csv".format(t_share.args['output_Directory'], t_share.args["Input_File"].split("/")[-1]), "x") as result_file:
        population_stat_collection_bk = copy.deepcopy(population_stat_collection)
        result_file.write("Population")
        controller = False
        for pop_name, collect in population_stat_collection.items():
            if not controller:
                for index in range(1,len(collect)):
                    result_file.write(",Ho,He".format(index, index))
                controller = True
            result_file.write("\n{}".format(pop_name.strip(",")))
            for collect_key in collect.keys():
                for k,v in collect[collect_key][-1].items():
                    collect[collect_key][-1][k] = Decimal(v / sum(population_stat_collection_bk[pop_name][collect_key][-1].values())) #collect[collect_key][-1].values()
            expected_heterozygosity = Decimal()
            for locus,alleles in population_stat_collection[pop_name].items():
                if locus == str(len(collect.keys())):
                    result_file.write("\n")
                for f1,f2 in  combinations(alleles[-1].keys(), 2):
                    expected_heterozygosity = ((2 * alleles[-1][f1]) * alleles[-1][f2]) + expected_heterozygosity
                heterozygotes = {}
                homozygotes = {}
                for k,v in Counter(alleles[:-1]).items():
                    if '00' in k:
                        continue
                    elif k.split(",")[0] == k.split(",")[1]:
                        homozygotes[k] = v
                    else:
                        heterozygotes[k] = v
                observed_heterozygotes = sum(heterozygotes.values()) / (sum(heterozygotes.values()) + sum(homozygotes.values()))
                result_file.write(",{},{}".format(observed_heterozygotes,expected_heterozygosity))
                expected_heterozygosity = 0

def threshold_filter(data):
    '''
    :function threshold_filter
        This function will take a dataset separated by individuals and parse/process all the alleles in by locus to
        provide a list of alleles that fall outside the user defined threshold.
    :param
        data = data expected to be sorted individuals.
            csv:
                02,02,07,00,08,08,04,06,02,09,10,11,03,04,09,09,06,06
                04,06,09,12,08,08,04,04,09,11,08,09,04,05,09,09,06,08
            pop:
                all_data, 13 16 21 21
                all_data, 13 16 21 21
    :raises
        Will raise on missing data. null data should be expressed as 0.
    :returns
        This function will return a list of locus with alleles outside the user defined threshold.
            -example
                [[locus0],[locus1]]
                [[4,6],[9]]
    '''
    global t_share
    alleles_below_threshold_by_locus = []
    for locus_num in range(0,len(data[0]),2):
        alleles_merge = [data[alleles][locus_num : locus_num +2] for alleles in range(len(data))]
        allele_freqs = Counter([str(int(allele)) for column in zip(*alleles_merge) for allele in column if int(allele) != 0])
        allele_sum = sum(allele_freqs.values())
        for allele in allele_freqs.keys():
            allele_freqs[allele] = Decimal(allele_freqs[allele] / allele_sum)
        alleles_below_threshold = [allele for allele in allele_freqs.keys() if allele_freqs[allele] < Decimal(t_share.args.get('Threshold', '0'))]
        alleles_below_threshold_by_locus.append(alleles_below_threshold)
    return alleles_below_threshold_by_locus

def permutes(genotypes_by_locus):
    '''
    This function will take the duplicate randomize the original dataset by locus/genotype.
    :param genotypes_by_locus_threshold:
    :return: list of list; index0 = original dataset, index 1+ = datasets are randomized by locus/genotype
    '''
    global t_share
    dataset = []
    t_share.sub_status = '10'
    for permute_index in range(int(t_share.args.get('permute_number','0')) + 1):
        permute = []
        for locus in genotypes_by_locus:
            if permute_index == 0: #maintain source data in index 0
                permute.append(locus)
            else:
                temp_permute = locus*1
                for random_int in range(random.randrange(2,9)):
                    random.shuffle(temp_permute)
                permute.append(temp_permute)
        dataset.append(permute)
    return dataset

def composite_haplotype_table_generator(population, ispermute = True):
    '''
    :function composite_haplotype_table_generator
        #1 = This will be a list of all haplotypes; each haplotype will be associated with a dictionary that contains
            its results. see returns
        #2 = This will loop from locus "0" to the second to last locus.  It only loops to the second-to-last because the
            last locus will be the "second locus" below.  Similarly, locus "0" will always be the first locus.
        #3 = This provides a range for locus 2 from the "first locus plus one" through the last locus.  This is a loop
            within a loop so that all possible locus pairings are achieved, but not duplicated.
        #4 = The length of the population is equal to the number of individuals. For each individual, multi-locus genotype
            Aa Bb is converted to the four haplotypes AB, Ab, aB, and ab using the imported "product" function from
            itertools: Note null data '0' is removed at this point. For each haplotype, i represents the allele for
            locus 1, j represents the allele for locus 2.
        #5 = This will store the Dictionary returned from function "calc_r_squared". see note #1 for description of the
            dictionary.
    :param
        population = [[locus0],[locus1],[locus2],[locus3],...]
                     [['13,16', '12,16', '16,13', '16,13'],['21,21', '21,21', '21,24', '21,24']]
    :raises
        Will raise exception for data with less than three loci.
    :returns
        Dictionary_key{'S_lm' = list(int(sample size), float(mean S)),
                       'loci_unique_1' = list(all unique alleles),
                       'loci_unique_1_num' = int(count of unique alleles),
                       'loci_unique_2' = list(all unique alleles),
                       'loci_unique_2_num' = int(count of unique alleles),
                       'loci_1' = int(loci index of haplotype table first position),
                       'loci_2' = int(loci index of haplotype table second position),
                       'r2lm_weighing_factor_numerator' = list(Decimal),
                       'r_squared_lm' = list(Decimal(r squared lm comp),Decimal(r squared lm delta)),}
    '''
    composite_haplotype_table = [] #1
    for first_locus in range(len(population) - 1): #2
        for second_locus in range(first_locus+1,len(population)):
            composite_haplotype_table_loci = []
            for individual in range(len(population[first_locus])):#3
                if t_share.args.get('Use_missing_data', 'False') == 'True' and  '0' in \
                        population[first_locus][individual].split(",") or '0' in \
                        population[second_locus][individual].split(","): #4
                    continue
                elif population[first_locus][individual] == '0,0' or population[second_locus][individual] == '0,0':
                    continue
                else:
                    for i,j in product(population[first_locus][individual].split(","), population[second_locus][individual].split(",")):
                        composite_haplotype_table_loci.append("{},{}".format(i,j))
            composite_haplotype_table.append(calc_r_squared(composite_haplotype_table_loci, first_locus, second_locus ,population, ispermute)) #5
    return composite_haplotype_table

def homozygote_freq(population, first_locus, second_locus, haplotype):
    '''
    :function homozygote_freq
        #1 = #homozygote at locus_1 and locus_2  Note: split will take ("5,6") and turn it into a list [5,6]
        #2 = list of all genotypes at locus_1 and locus_2 and remove null genotype data from the population.
        #3 = Calculate frequency of homozygote at first_locus and second_locus.
        #4 = This will return a list [homozygote freq at the first_locus ,homozygote freq at the second locus] #Note Decimal objects
    :param
        haplotype = str('4,9')
        first_locus = int(Index of first locus used in the haplotype table.)
        second_locus = int(Index of second locus used in the haplotype table.)
        population = list of loci(copy of the original input data after file processing.)
    :raises
    :returns
        homozygote_freqs = list(Decimal(locus_1_homozygote), Decimal(locus_2_homozygote))
    '''
    homozygote_freqs = []
    locus_1_homozygote = "{},{}".format(haplotype.split(",")[0],haplotype.split(",")[0]) #1
    locus_2_homozygote = "{},{}".format(haplotype.split(",")[1],haplotype.split(",")[1]) #1
    locus_1_genotypes = [population[first_locus][genotype] for genotype in range(len(population[first_locus])) if population[first_locus][genotype].split(',')[0]!='0' and population[first_locus][genotype].split(',')[1]!='0'] #2
    locus_2_genotypes = [population[second_locus][genotype] for genotype in range(len(population[second_locus])) if population[second_locus][genotype].split(',')[0]!='0' and population[second_locus][genotype].split(',')[1]!='0'] #2
    homozygote_freqs.append(Decimal(Counter(locus_1_genotypes)[locus_1_homozygote] / sum(Counter(locus_1_genotypes).values()))) #3
    homozygote_freqs.append(Decimal(Counter(locus_2_genotypes)[locus_2_homozygote] / sum(Counter(locus_2_genotypes).values()))) #3
    return homozygote_freqs #4

def calc_r_squared(composite_haplotype_table_loci,locus_1,locus_2, population, ispermute):
    '''
    :function calc_r_squared
        #1-4: Splits the first and second selected locus into two lists and preform and store counts(2&4).
        #5: Creates a list of all haplotypes via product function from the itertools module.
        #6-7: Two storage variables for storing sums of r_squared_lm_comp and r_squared_lm_delta during loop calculations.
        #8: This loop is used to unpack the all_potential_haplotypes list.
        #9-10: These lines are used to test the input data from the composite_haplotype_table_loci. If the counts from
               lines 2 or 4 do not exist it will apply 0 to the variable.
        #11-12: Create and store frequencies in the first and second locus.
        #13: calculation for D.
        #14: Calculation for "Denominator R Comp"
    :param
        composite_haplotype_table_loci = list('4,9', '4,12', '6,9', '6,12' ,'4,10')
        locus_1 = int(Index of first locus used in the haplotype table.)
        locus_2 = int(Index of second locus used in the haplotype table.)
        population = list of loci(copy of the original input data after file processing.)
    :raises
        Exception dependent on input data from composite_haplotype_table_generator
    :returns
        Dictionary_key{'S_lm' = list(int(sample size), float(mean S)),
                       'loci_unique_1' = list(all unique alleles),
                       'loci_unique_1_num' = int(count of unique alleles),
                       'loci_unique_2' = list(all unique alleles),
                       'loci_unique_2_num' = int(count of unique alleles),
                       'loci_1' = int(loci index of haplotype table first position),
                       'loci_2' = int(loci index of haplotype table second position),
                       'r2lm_weighing_factor_numerator' = list(Decimal),
                       'r_squared_lm' = list(Decimal(r squared lm comp),Decimal(r squared lm delta)),}
    '''
    global t_share
    locus_1_alleles = [(alleles.split(',')[0]) for alleles in composite_haplotype_table_loci] #1
    locus_1_allele_count = Counter(locus_1_alleles) #2
    locus_2_alleles = [(alleles.split(',')[1]) for alleles in composite_haplotype_table_loci] #3
    locus_2_allele_count = Counter(locus_2_alleles) #4
    all_potential_haplotypes = ["{},{}".format(i,j) for i,j in product(sorted(set(locus_1_alleles)),sorted(set(locus_2_alleles))) if i is not "0" and j is not '0'] #5
    r_squared_lm_comp = 0 #6
    r_squared_lm_delta = 0 #7
    results = OrderedDict()
    pi = [Decimal(locus_1_allele_count.get(haplotype.split(",")[0], 0 )/len(locus_1_alleles)) for haplotype in all_potential_haplotypes] #pi is the frequency of the allele at locus 1
    qj = [Decimal(locus_2_allele_count.get(haplotype.split(",")[1], 0 )/len(locus_2_alleles)) for haplotype in all_potential_haplotypes] #qj is the frequency of the allele at locus 2
    piqj_exclude = []
    piqj = [pi[i] * qj[i] for i in range(len(pi))]
    haplotype_data = []
    for index,haplotype in enumerate(all_potential_haplotypes): #8
        subdata = OrderedDict()
        subdata['kl'] = locus_1
        subdata['km'] = locus_2
        subdata['haplotype'] = haplotype
        subdata['Excluded'] = 'No'
        subdata['kl_Homozygote_Freq'], subdata['km_Homozygote_Freq'] = homozygote_freq(population, subdata['kl'], subdata['km'], subdata['haplotype'])
        subdata['D'] = Decimal(Counter(composite_haplotype_table_loci).get(haplotype, 0) / Decimal(sum(Counter(composite_haplotype_table_loci).values())) - ((pi[index]) * (qj[index]))) #13 use filter alleles zeros and threshold
        subdata['pi'], subdata['qj'], subdata['piqj'] = pi[index], qj[index], piqj[index]
        subdata['Denominator_R_comp'] = (subdata['pi'] * (1 - subdata['pi'])) * (subdata['qj'] * (1 - subdata['qj'])) #14 ###mod
        subdata['Denominator_R_delta'] = ((subdata['pi']*(Decimal(1 - subdata['pi'])))+(subdata['kl_Homozygote_Freq']-Decimal(math.pow(subdata['pi'], 2)))) * ((subdata['qj']*(Decimal(1 - subdata['qj'])))+(subdata['km_Homozygote_Freq']-Decimal(math.pow(subdata['qj'], 2)))) #Sved 2013 Equation 5
        if subdata['pi'] < t_share.args['Threshold'] or subdata['qj'] < t_share.args['Threshold']:
            piqj_exclude.append(index)
            subdata["Excluded"] = "Yes"
        if  subdata['Denominator_R_comp'] == Decimal(0) or subdata['Denominator_R_delta'] == Decimal(0): continue  #move to next haplotype
        else:
            t_share.counter += 1 #Legacy based on the average method
            subdata['piqj_sum'] = sum([piqj_product for index0,piqj_product in enumerate(piqj) if index0 not in piqj_exclude]) if t_share.args['Threshold'] != Decimal(0.0) else Decimal(1)
            subdata['unweighted_rij_comp'] = (4*(Decimal(math.pow(subdata['D'], 2)))) / subdata['Denominator_R_comp'] if subdata['Denominator_R_comp'] != Decimal(0) or subdata["Excluded"] == "No" else Decimal(0)
            subdata['unweighted_rij_delta'] = (4*(Decimal(math.pow(subdata['D'], 2)))) / subdata['Denominator_R_delta'] if subdata['Denominator_R_delta'] != Decimal(0) or subdata["Excluded"] == "No" else Decimal(0)
            subdata['weighting_factor'] = subdata['piqj'] / subdata['piqj_sum'] if t_share.args['Threshold'] == Decimal(0.0) else Decimal(1)
            subdata['weighted_rij_comp'] = ((subdata['unweighted_rij_comp'] * piqj[index]) / subdata['piqj_sum']) if subdata['unweighted_rij_comp'] != Decimal(0) or subdata["Excluded"] == "No" else Decimal(0)
            subdata['weighted_rij_delta'] = ((subdata['unweighted_rij_delta'] * piqj[index]) / subdata['piqj_sum']) if subdata['unweighted_rij_delta'] != Decimal(0) or subdata["Excluded"] == "No" else Decimal(0)
            if subdata["Excluded"] == "Yes":
                continue
            r_squared_lm_comp += subdata['weighted_rij_comp']
            r_squared_lm_delta += subdata['weighted_rij_delta']
            haplotype_data.append(subdata)
    results['r_squared_lm'] = [r_squared_lm_comp, r_squared_lm_delta] #[r_squared_lm_comp, r_squared_lm_delta]
    results['locus1'] = locus_1
    results['locus2'] = locus_2
    results['loci_unique_1'] = set(locus_1_alleles)  #kl
    results['loci_unique_1_num'] = len(set(locus_1_alleles))
    results['loci_unique_2'] = set(locus_2_alleles) #km
    results['loci_unique_2_num'] = len(set(locus_2_alleles))
    results['S_lm'] = [len(population[0]), (len(composite_haplotype_table_loci) / 4)] #[sample_size, mean_S, harmonic_mean_of_sample_size]
    results['r2lm_weighting_factor_numerator'] = [Decimal(math.pow(results['S_lm'][1] , 2)*((results['loci_unique_1_num'] -1) * (results['loci_unique_2_num'] -1)))]
    if not ispermute: t_share.datasheets.append(haplotype_data)
    t_share.counter = 0
    return results

def weighted_r2_calc(results):
    '''
    :Function weighted_r2_calc
        #1: variable used to store summing functions.
        #2: list variable stores a list of weighing factor by locus pair.
        #3: list variable stores a list of weighted r_squared by locus pair.
        #4: loop used to access r squared lm comp & r squared lm delta within r_squared_lm list.
        #5: Used to sum and store the r2lm weighting factor denominator.
        #6: Used to create and store the weighting factors by locus pair.
        #7: Check is r2lm_weighting_factor_S_method is 0. If not continue into calc weighted_r2_by_locus_pair.
        #8-9: Calculate and store a list of weighted_r2_by_locus_pair
        #10: cycle through haplotypes by locus pair.
        #11-12: create and store weighting_factor_by_locus_pair and weighted_r2_by_locus_pair.
        #13-17: Loop is used to through S methods to parse and store the correct value per locus pair.

    :param
        list of haplotypes(Dictionary_key{'S_lm' = list(int(sample size), float(mean S)),
                                          'loci_unique_1' = list(all unique alleles),
                                          'loci_unique_1_num' = int(count of unique alleles),
                                          'loci_unique_2' = list(all unique alleles),
                                          'loci_unique_2_num' = int(count of unique alleles),
                                          'loci_1' = int(loci index of haplotype table first position),
                                          'loci_2' = int(loci index of haplotype table second position),
                                          'r2lm_weighing_factor_numerator' = list(Decimal),
                                          'r_squared_lm' = list(Decimal(r squared lm comp),Decimal(r squared lm delta)),})
    :raises
    :returns
        list of haplotypes(Dictionary_key{'S_lm' = list(int(sample size), float(mean S)),
                                          'loci_unique_1' = list(all unique alleles),
                                          'loci_unique_1_num' = int(count of unique alleles),
                                          'loci_unique_2' = list(all unique alleles),
                                          'loci_unique_2_num' = int(count of unique alleles),
                                          'loci_1' = int(loci index of haplotype table first position),
                                          'loci_2' = int(loci index of haplotype table second position),
                                          'r2lm_weighing_factor_numerator' = list(Decimal),
                                          'r_squared_lm' = list(Decimal(r squared lm comp),Decimal(r squared lm delta)),
                                          'wighted_r2' = list(Decimal(weighting factor r2 comp with sample size),Decimal(weighting factor r2 with mean S)),
                                          'weighting_factor' = list(Decimal(weighting factor comp with sample size),Decimal(weighting factor with mean S)))})

    '''
    r2lm_weighting_factor_denominator = [] #1
    weighting_factor_by_locus_pair = [] #2
    weighted_r2_by_locus_pair = [] #3
    for r_type in range(len(results[0]['r_squared_lm'])): #4
        r2lm_weighting_factor_denominator.append(Decimal(sum([locus_pair['r2lm_weighting_factor_numerator'][0] for locus_pair in results]))) #5
        weighting_factor_by_locus_pair.append([locus_pair['r2lm_weighting_factor_numerator'][0] / r2lm_weighting_factor_denominator[0] for locus_pair in results]) #6
        weighted_r2_by_locus_pair.append([locus_pair['r_squared_lm'][r_type] * (locus_pair['r2lm_weighting_factor_numerator'][0] / r2lm_weighting_factor_denominator[r_type]) for locus_pair in results])
    for locus_pair in range(len(results)): #10
        weighted_r2 = [] #11
        weighting_factor = [] #12
        for r_type in range(len(results[0]['r_squared_lm'])): #13
            weighted_r2.append(weighted_r2_by_locus_pair[r_type][locus_pair]) #14
            weighting_factor.append(weighting_factor_by_locus_pair[r_type][locus_pair]) #15
        results[locus_pair]['weighted_r2'] = weighted_r2 #16
        results[locus_pair]['weighting_factor'] = weighting_factor #17
    return results

def methods(composite_haplotype_table): # Going to have to seperate function at second for loop for permutes.....
    '''
    :Function methods
        #1-4: create list and dictionary collections for use in the function.
    :param
        list of haplotypes(Dictionary_key{'S_lm' = list(int(sample size), float(mean S)),
                                          'loci_unique_1' = list(all unique alleles),
                                          'loci_unique_1_num' = int(count of unique alleles),
                                          'loci_unique_2' = list(all unique alleles),
                                          'loci_unique_2_num' = int(count of unique alleles),
                                          'loci_1' = int(loci index of haplotype table first position),
                                          'loci_2' = int(loci index of haplotype table second position),
                                          'r2lm_weighing_factor_numerator' = list(Decimal),
                                          'r_squared_lm' = list(Decimal(r squared lm comp),Decimal(r squared lm delta)),
                                          'wighted_r2' = list(Decimal(weighting factor r2 comp with sample size),Decimal(weighting factor r2 with mean S)),
                                          'weighting_factor' = list(Decimal(weighting factor comp with sample size),Decimal(weighting factor with mean S)))})
    :raises
    :returns
    '''
    method_S = [] #1, #[input_S, Mean_S, Harmonic_Mean_S]
    methods_R2_dict = OrderedDict() #2
    methods_S_dict = OrderedDict() #3
    methods_r2 = [] #4, #[by_comp, by_delta]
    for r_squared_lm_type in range(len(composite_haplotype_table[0]['weighted_r2'])): #
        final_r2 = sum(locus_pair['weighted_r2'][r_squared_lm_type] for locus_pair in composite_haplotype_table)
        methods_r2.append(final_r2)
    for S_method in range(len(composite_haplotype_table[0]['S_lm'])):
        S = sum([ locus_pair['S_lm'][S_method] for locus_pair in composite_haplotype_table])  / len(composite_haplotype_table)
        method_S.append(S)
    harmonic_S =  len(composite_haplotype_table) / (sum([(1 / locus_pair['S_lm'][1]) for locus_pair in composite_haplotype_table if locus_pair['S_lm'][1] != 0]))
    method_S.append(harmonic_S)
    methods_S_dict['input_S'] = method_S[0]
    methods_S_dict['Mean_S'] = method_S[1]
    methods_S_dict['Harmonic_Mean_S'] = method_S[2]
    methods_R2_dict["r^Comp"] = methods_r2[0]
    methods_R2_dict["r^Delta"] = methods_r2[1]
    methods = [methods_R2_dict, methods_S_dict]
    return methods

def permute_Ne(composite_haplotype_table, method_R2_S):
    '''
    :param
    :raises
    :structure guides
        methods_names = {"0": "input_S", "1": "Mean_S", "2": "Harmonic_Mean_S"}
        methodr_names = {"0": "r^2_comp", "1": "r^2_delta"}
    :returns
    '''
    final_results = []  # results based on #[sample_size, mean_S, harmonic_mean_of_sample_size]
    for r2_type in range(len(method_R2_S[0])):
        final_result = OrderedDict()
        for r2_methods in method_R2_S[0][r2_type].keys():
            final_result['{}_Ne'.format(r2_methods)] = 1 / (3 * (method_R2_S[0][r2_type][r2_methods]))
            final_result[r2_methods] = method_R2_S[0][r2_type][r2_methods]
        final_results.append(final_result)
    return final_results

def Ne(method_R2_S):
    '''
    :param
    :raises
    :structure guides
        methods_names = {"0": "input_S", "1": "Mean_S", "2": "Harmonic_Mean_S"}
        methodr_names = {"0": "r^2_comp", "1": "r^2_delta"}
    :returns
    '''

    final_results = []  # results based on #[sample_size, mean_S, harmonic_mean_of_sample_size]
    for S_method in method_R2_S[1].keys():
        for r2_methods in method_R2_S[0].keys():
            final_result = OrderedDict()
            final_result['sample_size_correction_factor'] = (Decimal(1 / method_R2_S[1][S_method])) * (
            1 - (1 / Decimal(math.pow(((2 * method_R2_S[1][S_method]) - 1), 2))))
            final_result['Ne'] = 1 / (3 * (method_R2_S[0][r2_methods] - final_result['sample_size_correction_factor']))
            final_result[r2_methods] = method_R2_S[0][r2_methods]
            final_result[S_method] = method_R2_S[1][S_method]
            final_results.append(final_result)
    return final_results

def permute_stat(comp_r2_permutes,delta_r2_permutes,method_R2_S):
    '''
    :param
    :raises
    :structure guides
        {"0":"input_S", "1":"Mean_S", "2":"Harmonic_Mean_S"}
    :returns
    '''
    legend = {"0" : "Comp", "1" : "Delta"}
    global t_share
    r2_permutes_list = [comp_r2_permutes,delta_r2_permutes ]
    r2_methods = []
    for r2_permutes in range(len(r2_permutes_list)):
        r2_permutes_dict = OrderedDict()
        ordered_r2_permutes = sorted(r2_permutes_list[r2_permutes])
        t_share.permute_corrections["r^{}_permutation_correction_factor".format(legend[str(r2_permutes)])] = ordered_r2_permutes[t_share.confidence_interval['median']] if t_share.args.get('Use_Median', False) else statistics.mean(ordered_r2_permutes)
        t_share.permute_corrections["r^{}_permute_lower".format(legend[str(r2_permutes)])] = ordered_r2_permutes[t_share.confidence_interval['lower_limit']]
        t_share.permute_corrections["r^{}_permute_upper".format(legend[str(r2_permutes)])] = ordered_r2_permutes[t_share.confidence_interval['upper_limit']-1]
        r2_permutes_dict["r^{}_permute_corrected_upper".format(legend[str(r2_permutes)])] = method_R2_S[0]["r^{}".format(legend[str(r2_permutes)])] - t_share.permute_corrections["r^{}_permute_upper".format(legend[str(r2_permutes)])]
        r2_permutes_dict["r^{}_permute_corrected_lower".format(legend[str(r2_permutes)])] = method_R2_S[0]["r^{}".format(legend[str(r2_permutes)])] - t_share.permute_corrections["r^{}_permute_lower".format(legend[str(r2_permutes)])]
        r2_permutes_dict["r^{}_permute_corrected".format(legend[str(r2_permutes)])] = method_R2_S[0]["r^{}".format(legend[str(r2_permutes)])] - t_share.permute_corrections["r^{}_permutation_correction_factor".format(legend[str(r2_permutes)])]#t_share.permute_median
        r2_methods.append(r2_permutes_dict)
    return [r2_methods,method_R2_S[1]]

def jackknife_controller(list_of_r2ij):
    '''
    :param
    :raises
    :returns
    '''
    jackknife_datasets = []
    t_share.sub_status = '9'
    for exclude_locus_pair in range(len(list_of_r2ij)):
        jackknife_dataset = []
        for results_by_locus_pair in range(len(list_of_r2ij)):
            if exclude_locus_pair == results_by_locus_pair:
                continue
            else:
                jackknife_dataset.append(list_of_r2ij[results_by_locus_pair])
        jackknife_datasets.append(jackknife_dataset)
        del jackknife_dataset
    jackknife_datasets_weighted = []
    jackknife_R_S_datasets = []
    for jackknife_dataset in jackknife_datasets:
            jackknife_dataset_weighted = weighted_r2_calc(jackknife_dataset)
            jackknife_R2_S_methods = methods(jackknife_dataset_weighted)
            jackknife_datasets_weighted.append(jackknife_dataset_weighted)
            jackknife_R_S_datasets.append(jackknife_R2_S_methods)
    del jackknife_datasets
    del jackknife_dataset
    jackknife_parametric_confidence_interval(r2_collection = [items[0]['r^Comp'] for items in jackknife_R_S_datasets], typef = "Comp")
    jackknife_parametric_confidence_interval(r2_collection = [items[0]['r^Delta'] for items in jackknife_R_S_datasets], typef = "Delta")
    jackknife_results = [] #[upper results,lower results]
    for jackknife_R2_S in jackknife_distribution_UL(jackknife_R_S_datasets):
        jackknife_results.append(Jackknife_Ne(jackknife_R2_S))
    return jackknife_formater(jackknife_results)

def jackknife_distribution_UL(jackknife_R_S_datasets):
    global t_share
    R2_Comps = sorted([R2_set[0]['r^Comp'] for R2_set in jackknife_R_S_datasets])
    R2_Deltas = sorted([R2_set[0]['r^Delta'] for R2_set in jackknife_R_S_datasets])
    confidence_interval_upper_limit = round(len(R2_Comps) * (1 - (t_share.args['alpha'] / 2)) -1)
    confidence_interval_lower_limit = round(len(R2_Comps) * (t_share.args['alpha'] / 2))
    R2_S_lower = [OrderedDict([('r^Comp' , R2_Comps[confidence_interval_lower_limit]),
                             ('r^Delta' , R2_Deltas[confidence_interval_lower_limit])]), jackknife_R_S_datasets[0][1]]
    R2_S_upper = [OrderedDict([('r^Comp' , R2_Comps[confidence_interval_upper_limit]), ('r^Delta' , R2_Deltas[confidence_interval_upper_limit])]), jackknife_R_S_datasets[0][1]]
    return [R2_S_upper, R2_S_lower]

def jackknife_formater(jackknife_results):
        return  {'Jack_Knife_Comp' : { 'input_S' : {'upper' : jackknife_results[1][0][0]['Ne'], 'lower' : jackknife_results[0][0][0]['Ne'],
                                                    'permute upper': jackknife_results[1][0][0]['pNe'], 'permute lower': jackknife_results[0][0][0]['pNe']},
                                      'Mean_S' : {'upper' : jackknife_results[1][1][0]['Ne'], 'lower' : jackknife_results[0][1][0]['Ne'],
                                                  'permute upper': jackknife_results[1][1][0]['pNe'], 'permute lower': jackknife_results[0][1][0]['pNe']},
                                      'Harmonic_Mean_S' : {'upper' : jackknife_results[1][2][0]['Ne'], 'lower' : jackknife_results[0][2][0]['Ne'],
                                                           'permute upper': jackknife_results[1][2][0]['pNe'], 'permute lower': jackknife_results[0][2][0]['pNe']}},
                 'Jack_Knife_Delta' : {'input_S': {'upper' : jackknife_results[1][0][1]['Ne'], 'lower' : jackknife_results[0][0][1]['Ne'],
                                                   'permute upper': jackknife_results[1][0][1]['pNe'], 'permute lower': jackknife_results[0][0][1]['pNe']},
                                       'Mean_S' : {'upper' : jackknife_results[1][1][1]['Ne'], 'lower' : jackknife_results[0][1][1]['Ne'],
                                                   'permute upper': jackknife_results[1][1][1]['pNe'], 'permute lower': jackknife_results[0][1][1]['pNe']},
                                       'Harmonic_Mean_S' : {'upper' : jackknife_results[1][2][1]['Ne'], 'lower' : jackknife_results[0][2][1]['Ne'],
                                                            'permute upper': jackknife_results[1][2][1]['pNe'], 'permute lower': jackknife_results[0][2][1]['pNe']}}}

def jackknife_parametric_confidence_interval(r2_collection = [], typef = "" ):
    '''
    :param
    :raises
    :returns
    '''
    global t_share
    n = len(r2_collection)
    mean_r2 = statistics.mean(r2_collection)
    sum_of_error = sum(math.pow(r2 - mean_r2,2) for r2 in r2_collection)
    variance_r2 = sum_of_error / math.pow(n,2)
    for result in t_share.final_results:
        keys = list(result.keys())
        R_ = 0
        for key in keys:
            if typef in key:
                R_ = result[key]
        if R_:
            theta = variance_r2 / math.pow(statistics.mean(r2_collection),2)
            effective_number_of_comparisons = 2/theta
            r_chi_lower = stats.chi2.ppf(t_share.args['alpha']/2,effective_number_of_comparisons)
            r_chi_upper = stats.chi2.ppf(float(1-(t_share.args['alpha'])/2),effective_number_of_comparisons)
            r_lower_bound = Decimal((effective_number_of_comparisons * float(R_)) / r_chi_lower)
            r_upper_bound = Decimal((effective_number_of_comparisons * float(R_)) / r_chi_upper)
            result["parametric_upper_CI"] = 1/(3*(float(r_upper_bound) - float(result['sample_size_correction_factor'])))
            result["parametric_lower_CI"] = 1/(3*(float(r_lower_bound) - float(result['sample_size_correction_factor'])))


def Jackknife_Ne(method_R2_S):
    '''
    :param
        methods_names = {"0": "input_S", "1": "Mean_S", "2": "Harmonic_Mean_S"}
        methodr_names = {"0": "r^2_comp", "1": "r^2_delta"}
        method_R2_S = methods(composite_haplotype_table)
    :raises
    :returns
    '''
    final_results = []  # results based on #[sample_size, mean_S, harmonic_mean_of_sample_size]
    for S_method in method_R2_S[1].keys():
        tmp_final_result = []
        for r2_methods in method_R2_S[0].keys():
            final_result = OrderedDict()
            sample_size_correction_factor = (Decimal(1 / method_R2_S[1][S_method])) * (1 - (1 / Decimal(math.pow(((2 * method_R2_S[1][S_method]) - 1), 2))))
            final_result['Ne'] = 1 / (3 * (method_R2_S[0][r2_methods] - sample_size_correction_factor))
            final_result[r2_methods] = method_R2_S[0][r2_methods]
            final_result[S_method] = method_R2_S[1][S_method]
            if t_share.args.get("Use_Permute", 'False') == 'True':
                final_result['pNe'] = 1 / (3 * (method_R2_S[0][r2_methods] - t_share.permute_corrections["{}_permutation_correction_factor".format(r2_methods)]))
            tmp_final_result.append(final_result)
        final_results.append(tmp_final_result)
    return final_results

def output_file(population_name):
    global t_share
    if not t_share.date_good:
        t_share.datetime_update()
        t_share.date_good = True
    t_share.population_name = population_name.strip(",")
    t_share.output_file = "{}/{}_{}.txt".format(t_share.args['output_Directory'],t_share.args['Result_file_name'],t_share.population_name if t_share.population_name else t_share.args['Result_file_name'].split("/")[-1])
    outfile = open(t_share.output_file,'x')
    outfile.close()
    t_share.date_good = False

def header1():
    '''
    :param
    :raises
    :returns
    '''
    global t_share
    with open(t_share.output_file, 'a') as ofile:
        if t_share.population_name:
            ofile.write("Population_name: {}\nMinimum Frequency: {}\nAlpha: {}\n".format(t_share.population_name, t_share.args.get('Threshold','0.00'), t_share.args['alpha']))
        else:
            ofile.write("\tFiles_name: {}\n\tMinimum Frequency: {}\n\tAlpha: {}\n".format(t_share.args['Input_File'], t_share.args.get('Threshold','0.00'), t_share.args['alpha']))
        ofile.write("{}\n".format("==" * 40))

def header2():
    '''
    :param
    :raises
    :returns
    '''
    with open(t_share.output_file, 'a') as ofile:
        ofile.write("{}\n".format("="*209))
        ofile.write("|Locus Pair\t|\tkl\t|\tkm\t|\tSlm \t|\tWeighting Factor\t|\tRlm Comp\t|\tWeighted Rlm Comp\t|\tRlm Delta\t|\tWeighted Rlm Delta\t|\n")
        ofile.write("{}\n".format("-"*209))

def reporter(final_result,jack_knife):
    '''
    :param
    :raises
    :returns
    '''
    global t_share
    with open(t_share.output_file, 'a') as ofile:
        for key,value in final_result.items():
            ofile.write("{} = {}\n".format(key, value))
        if t_share.args.get("Use_Jackknife", 'False') == 'True':
            if "input_S" in final_result.keys():
                for k in ["upper", "lower"]:
                    ofile.write("jackknife_{} = {}\n".format(k, jack_knife['Jack_Knife_Comp' if "r^Comp" in final_result.keys() else 'Jack_Knife_Delta']['input_S'][k]))
            elif "Mean_S" in final_result.keys():
                for k in ["upper", "lower"]:
                    ofile.write("jackknife_{} = {}\n".format(k, jack_knife['Jack_Knife_Comp' if "r^Comp" in final_result.keys() else 'Jack_Knife_Delta']['Mean_S'][k]))
            elif "Harmonic_Mean_S" in final_result.keys():
                for k in ["upper", "lower"]:
                    ofile.write("jackknife_{} = {}\n".format(k, jack_knife['Jack_Knife_Comp' if "r^Comp" in final_result.keys() else 'Jack_Knife_Delta']['Harmonic_Mean_S'][k]))
        ofile.write("{}\n".format("==" * 40))

def reporter1(r2_permute_final_results):
    with open(t_share.output_file, 'a') as ofile:
        for index,_type in enumerate(t_share.cd_controller):
            for key in t_share.permute_controller:
                ofile.write("{} = {}\n".format("{}{}".format(_type,key), r2_permute_final_results[index]["{}{}".format(_type,key)]))
            for jk_key in t_share.permute_jk_controller:
                ofile.write("jackknife_{} = {}\n".format(jk_key, t_share.jack_knife['Jack_Knife_Comp' if "r^Comp" in _type else 'Jack_Knife_Delta']['Mean_S'][jk_key]))
            ofile.write("{}\n".format("==" * 40))
        ofile.write("{}\n".format("==" * 40))

def sample_report(locus_pair, tag = 0):
    '''
    :param
    :raises
    :returns
    '''
    if tag:
        return "\t{},{}\t\t{}\t\t{}\t\t{:.2f}\t\t\t{:.5f}\t\t\t{:.5f}\t\t\t\t{:.5f}\t\t\t{:.5f}\t\t\t{:.5f}\n". \
                                                                                        format(locus_pair['locus1'], \
                                                                                        locus_pair['locus2'], \
                                                                                        locus_pair['loci_unique_1_num'], \
                                                                                        locus_pair['loci_unique_2_num'], \
                                                                                        locus_pair['S_lm'][1], \
                                                                                        locus_pair['weighting_factor'][0], \
                                                                                        locus_pair['r_squared_lm'][0], \
                                                                                        locus_pair['weighted_r2'][0], \
                                                                                        locus_pair['r_squared_lm'][1], \
                                                                                        locus_pair['weighted_r2'][1])
    else:
        return "\t\t{},{}\t\t\t\t{}\t\t{}\t   {:.2f}\t\t\t{:.5f} \t\t   {:.5f} \t\t\t\t{:.5f}\t\t\t\t{:.5f}\t\t\t{:.5f} ". \
                                                                                        format(locus_pair['locus1'], \
                                                                                        locus_pair['locus2'], \
                                                                                        locus_pair['loci_unique_1_num'], \
                                                                                        locus_pair['loci_unique_2_num'], \
                                                                                        locus_pair['S_lm'][1], \
                                                                                        locus_pair['weighting_factor'][0], \
                                                                                        locus_pair['r_squared_lm'][0], \
                                                                                        locus_pair['weighted_r2'][0], \
                                                                                        locus_pair['r_squared_lm'][1], \
                                                                                        locus_pair['weighted_r2'][1])

def debug_datasheet():
    global t_share
    with open("{}_datasheets.csv".format(t_share.output_file), 'a') as ofile:
        key_con = (len(t_share.datasheets[0][000].keys()))
        for keylen,column_name in enumerate(t_share.datasheets[0][000].keys()): #create key line for csv file
            ofile.write("{}{}".format(column_name, "," if keylen < key_con else ""))
        ofile.write("\n")
        for index in range(len(t_share.datasheets)):
            control = len(t_share.datasheets[index])
            for num,haplotypes in enumerate(t_share.datasheets[index]):
                for value in haplotypes.values():
                    if isinstance(value, Decimal):
                        ofile.write("{:7f}{}".format(value, "," if num < control else ""))
                    else:
                        ofile.write("{}{}".format(value.replace(",",";") if isinstance(value, str) else value, "," if num < control else ""))
                ofile.write("\n")
    t_share.datasheets = []

def find(path = "PyNE/input_datafiles"):
    data_files = []
    for root, dirs, files in os.walk(path):
        for file in files:
            if file.endswith(("txt","csv")):
                data_files.append(os.path.join(root, file))
    return data_files

def update_args(datafile):
    global t_share
    t_share.args['Input_File'] = datafile
    t_share.datetime_update()
    t_share.args['output_Directory'] = "PyNE/results/{}{}".format(t_share.args['Input_File'].split(".")[0].split("/")[1],t_share.date)
    t_share.args['Result_file_name'] = "results{}".format(t_share.date)
    os.mkdir(t_share.args['output_Directory'])


def processor():
    '''
    :function : processor
    #1 Call functions that define how to process the input file.
    #2 The two for loops unpack the dataset that was returned from the input file.
    #3 Informs the user at the application is generating haplotype tables.
    #4 Passes the original dataset to the composite haplotype table generator.
    :param
    :raises
    :returns
    '''
    global t_share
    datafiles = find()
    for datafile in datafiles:
        update_args(datafile)
        genotypes_by_locus_by_population = process_input_file(t_share.args['Input_File'])#1
        t_share.number_of_populations = len(genotypes_by_locus_by_population)
        for index, genotypes_by_locus in enumerate(genotypes_by_locus_by_population): #2
            t_share.current_population_index = index
            output_file(list(genotypes_by_locus.keys())[0])
            for population_name in genotypes_by_locus.keys():
                t_share.sub_status = '3' #3
                t_share.list_of_r2ij = composite_haplotype_table_generator(genotypes_by_locus[population_name][0], False) #4
                t_share.composite_haplotype_tables_r_squared = weighted_r2_calc(t_share.list_of_r2ij)
                method_R2_S = methods(t_share.composite_haplotype_tables_r_squared)
                t_share.final_results = Ne(method_R2_S)
                if t_share.args.get("Use_Permute", 'False') == 'True':
                    t_share.sub_status = '6'
                    comp_r2_permutes = []
                    delta_r2_permutes = []
                    for permute in range(1,len(genotypes_by_locus[population_name])):
                        list_of_r2ij_permutes = composite_haplotype_table_generator(genotypes_by_locus[population_name][permute])
                        list_of_r2lm_permutes = weighted_r2_calc(list_of_r2ij_permutes)
                        method_R2_permute = methods(list_of_r2lm_permutes)
                        comp_r2_permutes.append(method_R2_permute[0]['r^Comp']) # appending list [r2_comp]
                        delta_r2_permutes.append(method_R2_permute[0]['r^Delta']) # appending list [r2_delta]
                    methods_R2_S = permute_stat(comp_r2_permutes,delta_r2_permutes,method_R2_S)
                    t_share.r2_permute_final_results = permute_Ne(t_share.composite_haplotype_tables_r_squared, methods_R2_S)
                    t_share.r2_permute_final_results[0]['r^Comp_permutation_correction_factor'] = t_share.permute_corrections["r^Comp_permutation_correction_factor"]
                    t_share.r2_permute_final_results[1]['r^Delta_permutation_correction_factor'] = t_share.permute_corrections["r^Delta_permutation_correction_factor"]
                if t_share.args.get("Use_Jackknife", 'False') == 'True':
                    t_share.sub_status = '5'
                    t_share.jack_knife = jackknife_controller(t_share.list_of_r2ij)
                t_share.sub_status = '7'
                header1()
                if t_share.args.get("Use_Permute", 'False') == 'True':
                    reporter1(t_share.r2_permute_final_results)
                for result in t_share.final_results:
                    reporter(result,t_share.jack_knife)
                header2()
                for locus_pair in t_share.composite_haplotype_tables_r_squared:
                    with open(t_share.output_file, 'a') as ofile:
                        ofile.write(sample_report(locus_pair,1))
                build_report01()
                if t_share.datasheets: debug_datasheet()
            if t_share.number_of_populations == t_share.current_population_index +1:
                t_share.datetime_update()
                web_client(t_share.port)
                sleep(15)
    t_share.status = '2'
    t_share.sub_status = '8'
    sleep(90)
    exit(0)

def main():
    '''
    :function :: main
    This function is the start of the application. It creates two threads  one for the webserver and another to launch
    the default webbrowser for the user interface. After, the threads are started thread main waits until the interface
    has been configured by the client.
    :param = controlled by the user interface and accessed via global t_share
    :return = none
    '''
    global t_share
    t_share.datetime_update()
    t_share.status = '0'
    try:
        os.mkdir("./PyNE")
        os.mkdir("./PyNE/results")
        os.mkdir("./PyNE/input_datafiles")
    except:
        pass
    t1 = thread(name='web server',target=server_daemon)
    t1.setDaemon(True)
    t2 = thread(name='web client',target=web_client(t_share.port))
    while t_share.status is not '4':
        t_share.reset_status()
        try:
            if not t1.isAlive():
                t1.start()
        except AttributeError:
            pass
        try:
            if t2.isAlive():
                t2.start()
                t2.join()
        except AttributeError:
            t2.run()
            t2.join()
        while t_share.status is '0':
            sleep(1)
        processor()
        exit(0)




if __name__ == '__main__':
    main()
