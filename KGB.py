import os
import pandas as pd
import warnings

import numpy as np

from tqdm import tqdm

from scipy.stats import entropy
import time
from sklearn.decomposition import PCA


def preprocess_df(df): 
    df['Sport'] = df['Sport'].fillna(-1)
    df['Dport'] = df['Dport'].fillna(-1)
    df["Backgroung_label"] = df.Label.str.contains("Background")
    df["Normal_label"] = df.Label.str.contains("Normal")
    df["Botnet_label"] = df.Label.str.contains("Botnet")
    df["StartTime"] = pd.to_datetime(df["StartTime"])
    df.sort_values("StartTime", inplace = True)
    return df


def compute_contexte_vector(df, window_time = 5, verbose = False, fillna= True):
    # window_time : the window_time which will be considered
    to_keep = ["StartTime","SrcAddr","DstAddr","Sport", "Dport","Label","Backgroung_label","Normal_label","Botnet_label"]
    df_for_entropies = df[to_keep]
    
    last_time = df_for_entropies.StartTime.max()
    time_min = last_time - pd.Timedelta(f"{window_time} minutes")
    df_for_entropies = df_for_entropies[df_for_entropies.StartTime>=time_min]

    #print(df_for_entropies)
    tmp_mesure = time.time_ns()
    base = 10
    entropy_agg =  lambda x : entropy(x.value_counts(), base=base)
    futur_df = pd.DataFrame({"SrcIP" : df_for_entropies.SrcAddr.unique()}).set_index("SrcIP")
    
    for i in range(window_time) :
        start = time_min + pd.Timedelta(f"{i} minutes")
        end = start + pd.Timedelta(f"{1} minutes")
        current_minute = df_for_entropies[(df_for_entropies.StartTime>=start) & (df_for_entropies.StartTime<end)]
    
        df_with_Entropies = current_minute.groupby(by = "SrcAddr").agg({'DstAddr': entropy_agg,
                                                                                'Dport': entropy_agg,
                                                                                 'Sport': entropy_agg})
        id_name = window_time-i-1
        df_with_Entropies.rename(columns = {"DstAddr" : f"H_DstAddr_t_{id_name}",
                                            "Dport" : f"H_Dport_t_{id_name}",
                                            "Sport" : f"H_Sport_t_{id_name}"}, inplace = True)
        futur_df = futur_df.merge(df_with_Entropies, left_index = True, right_index = True, how = "outer")
        
    if verbose : 
        print(f"Time required to compute aggregation : {np.round((time.time_ns() - tmp_mesure)/(10**9),2)} s")
    # Consequently, for successful detection, at least two flows per five minutes are needed.
    if fillna : # La j'ai un big doute
        futur_df = futur_df.fillna(0)  
    
    return futur_df


def compute_pca_over_vector(df, drop_limit = 10**-6):
    
    pca = PCA()
    new_flows = pca.fit_transform(df)
    
    cov_matrix= pca.get_covariance()

    eigen_values_vectors = []
    for i, eigenvector in enumerate(pca.components_):

        eigen_value = np.dot(eigenvector.T, np.dot(cov_matrix, eigenvector))

        eigen_values_vectors.append((eigen_value,eigenvector))
        if eigen_value <  drop_limit :
            break

    new_df = pd.DataFrame(new_flows[:,:i+1],columns = [f"component_{j}" for j in range(i+1)])
    new_df.set_index(df.index, drop = True, inplace = True)
    
    
    return new_df, eigen_values_vectors
           

def compute_anomaly_score(row, eigen, major_components = True,k=1):

    if major_components : 
        end = k
        start = 1 
    else :
        end = len(row)
        start = k+1 
        
    value_sum = 0
    for j in range(start,end+1) :
        e_val, e_vec = eigen[j-1]
        #print(row.values)
        #print()
        val = np.dot(e_vec,np.array(row.values))
        
        val/=e_val
        val=val**2
        value_sum+=val
    
    return value_sum


def proceed_KGB(df, anomaly_threshold, window_time = 5, fill_na_ctxt = True,
                drop_limit_eigen = 10**-6,
                major_components = True,k=1
               ) :
    """
    :df : obviously the df
    :anomaly_threshold : an int
    
    :window_time (opt) : int, the number of minutes considered in the df. we only consider the last window time in the df
    :fill_na_ctxt (opt) : when computing the context, Some Ip source doesn't produce enough netflows to reach to ratio of 
    1 per minute, thus we can't compute their entropy. if fillna is set to True, fills theses nan values with 0
    
    :drop_limit (opt) : Used to drop eigen values above a limit (default 10**-6: cf article). Supposed to be useful
    in order to maintain numerical stability.
    
    :k (opt) : the number of component to consider as first components in the anomaly score (default = 1 : cf article)
    :major_components (opt) : used if we want to use the methods of the principal components with the 
    highest variance (True) or the lowest (False)
    """
    
    context = compute_contexte_vector(df, window_time = window_time, fillna = fill_na_ctxt)
    
    new_components, eigen_values_vectors = compute_pca_over_vector(context, drop_limit = drop_limit_eigen)  
    
    
    res = context.apply(lambda x: compute_anomaly_score(x,eigen_values_vectors,major_components = major_components, k=k  ),
                                        axis = 1)
    #return res.sort_values(ascending=False)
    
    #return [ index for index, row in res.iteritems() if row>anomaly_threshold]
    
    return res[res>anomaly_threshold]

