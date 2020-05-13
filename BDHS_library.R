BDHS_data <- function(lambda.1, lambda.2,
                      m = 100, N = 50000,
                      shift.1 = 0, shift.C = 0, upper.1 = Inf) {
  
  U <- runif(n = N, min = 0, max = m - shift.C)
  C <- m - U
  
  ## gap time
  T1 <- rexp(n = N, rate = lambda.1) + shift.1
  T2 <- rexp(n = N, rate = lambda.2)
  
  for(i in 1:N) {
    while(T1[i] > upper.1) {
      T1[i] <- rexp(n = 1, rate = lambda.1) + shift.1
    }
  }
  
  ## total time
  Y1 <- T1
  Y2 <- T1 + T2
  df.comp <- data.frame(T1, T2)
  
  ## sampling from the finite population
  ind.sample <- Y1 <= C
  T1.trunc <- T1[ind.sample]
  T2.trunc <- T2[ind.sample]
  df.trunc <- data.frame(T1.trunc, T2.trunc, C[ind.sample])
  
  ## censored
  delta <- df.trunc[, 1] + df.trunc[, 2] <= df.trunc[, 3]
  T2.obs <- ifelse(delta, df.trunc[, 2], df.trunc[, 3] - df.trunc[, 1])
  df.obs <- data.frame(T1.obs = T1.trunc, T2.obs, delta, C[ind.sample])
  
  return(list(df.obs = df.obs,
              df.trunc = df.trunc,
              df.comp = df.comp))
}

## generate dependent data with clayton copula with alpha 1 (tau = 1 / 3)
BDHS_data_dep <- function(lambda.1, lambda.2,
                      m = 100, N = 50000,
                      shift.1 = 0, shift.C = 0, upper.1 = Inf) {
  
  U <- runif(n = N, min = 0, max = m - shift.C)
  C <- m - U
  
  ## dependent gap time
  w <- runif(n = N)
  uStar <- runif(n = N)
  v <- (2 - sqrt(4 - 4 * uStar)) / 2
  u1 <- (1 + w * (v ^ (-1) - 1)) ^ (-1)
  u2 <- (v ^ (-1) - w * (v ^ (-1) - 1)) ^ (-1)
  T1 <- -log(1 - u1) / lambda.1 + shift.1
  T2 <- -log(1 - u2) / lambda.2
  
  # for(i in 1:N) {
  #   while(T1[i] > upper.1) {
  #     T1[i] <- rexp(n = 1, rate = lambda.1) + shift.1
  #   }
  # }
  
  ## total time
  Y1 <- T1
  Y2 <- T1 + T2
  df.comp <- data.frame(T1, T2)
  
  ## sampling from the finite population
  ind.sample <- Y1 <= C
  T1.trunc <- T1[ind.sample]
  T2.trunc <- T2[ind.sample]
  df.trunc <- data.frame(T1.trunc, T2.trunc, C[ind.sample])
  
  ## censored
  delta <- df.trunc[, 1] + df.trunc[, 2] <= df.trunc[, 3]
  T2.obs <- ifelse(delta, df.trunc[, 2], df.trunc[, 3] - df.trunc[, 1])
  df.obs <- data.frame(T1.obs = T1.trunc, T2.obs, delta, C[ind.sample])
  
  return(list(df.obs = df.obs,
              df.trunc = df.trunc,
              df.comp = df.comp))
}

## estimate the marginal distribution of Y1 and C
lynden_func <- function(trunc.var, lifetime) {
  jump.point <- sort(lifetime)
  surv.prob <- numeric(length(lifetime) + 1)
  surv.prob[1] <- 1
  for(i in 1:length(jump.point)) {
    d <- sum(lifetime == jump.point[i])
    at.risk <- sum(lifetime >= jump.point[i] & jump.point[i] >= trunc.var)
    surv.prob[i + 1] <- surv.prob[i] * (1 - d / at.risk)
  }
  
  return(stepfun(jump.point, surv.prob))
}
##

## estimate the truncation probability
trunc_prob_func <- function(Y1, C, m = 100) {
  F_Y1_func <- lynden_func(m - C, m - Y1)
  S_C_func <- lynden_func(Y1, C)
  
  jump.point <- m - knots(F_Y1_func)
  mass.Y1 <- -diff(c(1, F_Y1_func(knots(F_Y1_func))))
  surv.C <- S_C_func(jump.point)
  pi.hat <- sum(surv.C * mass.Y1)
  
  return(pi.hat)
}
##

## estimate the marginal distribution of Y2
S_Y2_func <- function(Y1, Y2, delta, C, pi.hat, m = 100) {
  S_C_func <- lynden_func(Y1, C)
  F_Y1_func <- lynden_func(m - C, m - Y1)
  n <- length(Y1)
  
  jump.point <- sort(Y2[delta == 1])
  surv.est <- numeric(length(jump.point) + 1)
  surv.est[1] <- 1
  
  for(i in 1:length(jump.point)) {
    d <- pi.hat * sum(Y2 == jump.point[i] & delta == 1)
    risk.set.1 <- pi.hat * sum(Y2 >= jump.point[i])
    risk.set.2 <- n * (1 - F_Y1_func(m - jump.point[i])) * S_C_func(jump.point[i])
    risk.set.3 <- pi.hat * sum(Y1 > jump.point[i])
    
    surv.est[i + 1] <- surv.est[i] * (1 - d / (risk.set.1 + risk.set.2 - risk.set.3))
  }
  
  # return(stepfun(jump.point, surv.est))
  return(list(jumpPoint = jump.point, SurvEst = surv.est))
}
##

## estimate the joint distribution of T1 and T2
H2_func <- function(t1, t2, df, pi.hat, S_C_func) {
  n <- nrow(df)
  Y1 <- df[, 1]
  T2.censored <- df[, 2]
  
  return(mean((Y1 <= t1 & T2.censored > t2) / S_C_func(t2 + Y1)) * pi.hat)
}
##

## estimate the joint distribution of Y1 and Y2
H1_func <- function(s, t, df, pi.hat, Sc_func) {
  Y1 <- ifelse(length(colnames(df)) <= 4, df[, 1], df[, "Y1"])
  Y2 <- ifelse(length(colnames(df)) <= 4, df[, 1] + df[, 2], df[, "Y2"])
  
  return(pi.hat * mean(df[, 1] <= s & df[, 1] + df[, 2] > t) / Sc_func(t))
}

## estimate the marginal survival function of T2
S_T2_func <- function(t, df, pi.hat, Sc_func) {
  T2.censored <- df[, 2]
  Y1 <- df[, 1]
  
  return(pi.hat * mean((T2.censored > t) / Sc_func(Y1 + t)))
}
